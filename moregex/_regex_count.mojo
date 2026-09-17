"""Specialized regex count kernels."""

from ._ast import (
    CHAR_ASCII_WHITESPACE,
    BracketClassNode,
    CharClassNode,
    LiteralNode,
    MAX_BRANCHES,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits
from std.sys import CompilationTarget, llvm_intrinsic, simd_width_of
from std.utils import StaticTuple

from ._regex_common import (
    CLASS_SIMD_WIDTH,
    CLASS_TAIL_SIMD_WIDTH,
    _MatchSpanResult,
    _accepts_class,
    _bracket_accepts,
    _byte_range_mask,
    _match_checksum,
    _match_literal,
    _consume_simd_width_ladder,
    _search_simd_width_ladder,
    _zero_width_matches,
)

from ._regex_analysis import (
    _AnchoredLazyLiteralPlan,
    _LinePrefixRunLiteralPlan,
    _TwoDelimiterBracketRunsPlan,
    _anchored_prefix_delimited_line_offset,
    _all_prefixed_sequence_options,
    _bounded_repeat_byte_accepts,
    _bracket_mask,
    _fixed_node_mask,
    _fixed_node_width,
    _fixed_offset_mask,
    _fixed_prefilter_plan,
    _is_end_assertion_node,
    _is_bounded_line_gap_literal_alternation,
    _is_exact_bracket_range,
    _is_one_byte_class_node,
    _is_symmetric_bounded_delimited_sequence,
    _multiline_literal_edge_index,
    _node_start_accepts,
    _node_start_mask,
    _one_byte_atom_accepts,
    _same_bracket_ranges,
    _sequence_prefix_literal_index,
)

from ._regex_matcher import (
    _match_sequence_from,
    _match_node,
)
from ._regex_nfa import _nfa_match_at


from ._regex_literals import (
    _alternation_two_position_mask,
    _literal_alternation_block_fits,
    _literal_alternation_candidate_mask,
    _literal_alternation_match_length_at,
)


@always_inline
def _count_anchored_prefix_delimited_lines[
    regex: Regex
](text: ImmStringSpan) -> Int:
    """Count grep lines matching an AST-normalized prefix/delimiter shape."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime item_offset = _anchored_prefix_delimited_line_offset[
        regex.nodes, regex.root
    ]()
    comptime prefix = regex.nodes[sequence.items[1 + item_offset]][RepeatNode]
    var bytes = text.as_bytes()
    var length = text.byte_length()
    var total = 0
    var line_start = 0
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = length if newline < 0 else newline
        if line_end > line_start and Int(bytes[line_end - 1]) == ord("\r"):
            line_end -= 1
        var position = line_start
        while position < line_end and _node_start_accepts[
            regex.nodes, prefix.child
        ](Int(bytes[position])):
            position += 1
        if position < line_end and _node_start_accepts[
            regex.nodes, sequence.items[2 + item_offset]
        ](Int(bytes[position])):
            position += 1
            if position < line_end and _node_start_accepts[
                regex.nodes, sequence.items[4 + item_offset]
            ](Int(bytes[line_end - 1])):
                total += 1
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def _count_anchored_lazy_literal_lines[
    regex: Regex, plan: _AnchoredLazyLiteralPlan
](text: ImmStringSpan) -> Int:
    """Count anchored lines using the literal after a lazy dot as the anchor."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime prefix_literal = regex.nodes[plan.prefix_literal_index][
        LiteralNode
    ]
    comptime search_literal = regex.nodes[plan.search_literal_index][
        LiteralNode
    ]
    var total = 0
    var line_start = 0
    var length = text.byte_length()
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = newline
        if newline < 0:
            line_end = length
        if line_end > line_start and Int(text.as_bytes()[line_end - 1]) == 13:
            line_end -= 1
        var line = text[byte=line_start:line_end]
        var prefix = _match_node[regex.nodes, plan.prefix_repeat_index](line, 0)
        var prefix_end = prefix.unsafe_value().consumed()
        if _match_literal[prefix_literal.value](line, prefix_end):
            var candidate = line.find(
                search_literal.value,
                prefix_end + prefix_literal.value.byte_length(),
            )
            while candidate >= 0:
                var suffix = _match_sequence_from[
                    regex.nodes, sequence, plan.suffix_item
                ](
                    line,
                    candidate + search_literal.value.byte_length(),
                )
                if suffix:
                    total += 1
                    break
                candidate = line.find(search_literal.value, candidate + 1)
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def _count_line_prefix_run_literal[
    regex: Regex, plan: _LinePrefixRunLiteralPlan
](text: ImmStringSpan) -> Int:
    """Count lines matching a deterministic anchored run/literal prefix."""
    comptime literal = regex.nodes[plan.literal_index][LiteralNode]
    var total = 0
    var line_start = 0
    var length = text.byte_length()
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = newline
        if newline < 0:
            line_end = length
        if line_end > line_start and Int(text.as_bytes()[line_end - 1]) == 13:
            line_end -= 1
        var line = text[byte=line_start:line_end]
        var prefix = _match_node[regex.nodes, plan.repeat_index](line, 0)
        var position = prefix.unsafe_value().consumed()
        if (
            position + literal.value.byte_length() <= line.byte_length()
            and _match_literal[literal.value](line, position)
        ):
            total += 1
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def _count_leading_class_literal[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Find a required literal, then extend variable classes from that hit."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime leading_repeat = regex.nodes[sequence.items[0]][RepeatNode]
    comptime leading_child = leading_repeat.child
    comptime literal = regex.nodes[sequence.items[1]][LiteralNode]
    comptime literal_length = literal.value.byte_length()
    comptime end_anchored = _is_end_assertion_node[
        regex.nodes, sequence.items[2]
    ]()
    var length = text.byte_length()
    var bytes = text.as_bytes()
    var total = 0
    var search_start = 0
    var candidate: Int
    comptime if end_anchored:
        candidate = length - literal_length
        if candidate < 0 or not _match_literal[literal.value](text, candidate):
            if length == 0 or Int(bytes[length - 1]) != ord("\n"):
                return 0
            candidate = length - 1 - literal_length
            if candidate < 0 or not _match_literal[literal.value](
                text, candidate
            ):
                return 0
    else:
        candidate = text.find(literal.value)

    while candidate >= 0:
        var start = candidate
        while start > search_start and _one_byte_atom_accepts[
            regex.nodes, leading_child
        ](Int(bytes[start - 1])):
            start -= 1
        var leading_count = candidate - start
        if leading_count >= leading_repeat.minimum:
            var end = candidate + literal_length
            comptime if not end_anchored:
                while end < length and Int(bytes[end]) != ord("\n"):
                    end += 1
            total += _match_checksum[sum_spans](end - start)
            search_start = max(end, start + 1)
        else:
            search_start = candidate + 1

        comptime if end_anchored:
            break
        else:
            candidate = text.find(literal.value, search_start)
    return total


@always_inline
def _count_adjacent_dot_stars_around_literal[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count `.*.*literal.*` once per matching line in linear time."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime literal = regex.nodes[sequence.items[2]][LiteralNode]
    var total = 0
    var candidate = text.find(literal.value)
    while candidate >= 0:
        var line_start = candidate
        while line_start > 0 and Int(text.as_bytes()[line_start - 1]) != ord(
            "\n"
        ):
            line_start -= 1
        var line_end = text.find("\n", candidate + literal.value.byte_length())
        if line_end < 0:
            line_end = text.byte_length()
        total += _match_checksum[sum_spans](line_end - line_start)
        if line_end == text.byte_length():
            break
        candidate = text.find(literal.value, line_end + 1)
    return total


@always_inline
def _count_greedy_dot_complement_alternation[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count `.*[^class]|[class]` in one SIMD pass instead of quadratically."""
    var length = text.byte_length()
    comptime if sum_spans:
        # The ordered alternatives partition every byte. Matches therefore
        # cover the input exactly even though their grouping is greedy.
        return length
    if length == 0:
        return 0

    comptime alternation = regex.nodes[regex.root][OrNode]
    comptime first = regex.nodes[alternation.options[0]][SequenceNode]
    comptime terminal = regex.nodes[first.items[1]][BracketClassNode]
    var newline_count = 0
    var last_newline = -1
    var last_terminal = -1
    var offset = 0
    var pointer = text.unsafe_ptr()

    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while offset + width <= length:
            var values = pointer.unsafe_load[width=width, alignment=1](offset)
            var terminals = _bracket_mask[terminal, width](values)
            if any(terminals):
                var pending = pack_bits(terminals)
                while pending != 0:
                    var lane = Int(count_trailing_zeros(pending))
                    pending &= pending - 1
                    last_terminal = offset + lane
            var newlines = values.eq(SIMD[.uint8, width](UInt8(ord("\n"))))
            newline_count += newlines.reduce_bit_count()
            if any(newlines):
                var pending = pack_bits(newlines)
                while pending != 0:
                    var lane = Int(count_trailing_zeros(pending))
                    pending &= pending - 1
                    last_newline = offset + lane
            offset += width

    var bytes = text.as_bytes()
    while offset < length:
        var value = Int(bytes[offset])
        if _bracket_accepts[terminal](value):
            last_terminal = offset
        if value == ord("\n"):
            newline_count += 1
            last_newline = offset
        offset += 1

    var tail_start = last_newline + 1
    var tail_length = length - tail_start
    if tail_length == 0:
        return newline_count
    if last_terminal >= tail_start:
        return newline_count + 1 + length - last_terminal - 1
    return newline_count + tail_length


@always_inline
def _count_prefixed_nested_dot_literal[
    regex: Regex, literal_index: Int, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Scan required literals and test the required prefix once per line."""
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime prefix_index = root.items[0]
    comptime literal = regex.nodes[literal_index][LiteralNode]
    var total = 0
    var candidate = text.find(literal.value)
    var bytes = text.as_bytes()
    while candidate >= 0:
        var line_start = candidate
        while line_start > 0 and Int(bytes[line_start - 1]) != ord("\n"):
            line_start -= 1
        var matched_start = -1
        for start in range(line_start, candidate + 1):
            var prefix = _match_node[regex.nodes, prefix_index](text, start)
            if prefix and start + prefix.unsafe_value().consumed() <= candidate:
                matched_start = start
                break
        if matched_start >= 0:
            var line_end = text.find(
                "\n", candidate + literal.value.byte_length()
            )
            if line_end < 0:
                line_end = text.byte_length()
            total += _match_checksum[sum_spans](line_end - matched_start)
            if line_end == text.byte_length():
                break
            candidate = text.find(literal.value, line_end + 1)
        else:
            candidate = text.find(literal.value, candidate + 1)
    return total


@always_inline
def _count_repeated_lazy_dot_delimiter_suffix[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """SIMD-scan delimiter/suffix pairs, then validate preceding delimiters."""
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime repeated = regex.nodes[root.items[0]][RepeatNode]
    comptime child = regex.nodes[repeated.child][SequenceNode]
    comptime delimiter = regex.nodes[child.items[1]][LiteralNode]
    comptime suffix = regex.nodes[root.items[1]][LiteralNode]
    comptime delimiter_byte = Int(delimiter.value.as_bytes()[0])
    comptime suffix_byte = Int(suffix.value.as_bytes()[0])
    var total = 0
    var search_start = 0
    var bytes = text.as_bytes()
    var length = text.byte_length()
    var offset = 1
    while offset + CLASS_SIMD_WIDTH <= length:
        var previous_values = text.unsafe_ptr().unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](offset - 1)
        var suffix_values = text.unsafe_ptr().unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](offset)
        var candidates = previous_values.eq(
            SIMD[.uint8, CLASS_SIMD_WIDTH](UInt8(delimiter_byte))
        ) & suffix_values.eq(SIMD[.uint8, CLASS_SIMD_WIDTH](UInt8(suffix_byte)))
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var candidate = offset + lane
            if candidate <= search_start:
                continue
            var delimiter_count = 0
            var start = candidate
            while start > search_start and Int(bytes[start - 1]) != ord("\n"):
                start -= 1
                if Int(bytes[start]) == delimiter_byte:
                    delimiter_count += 1
            if delimiter_count >= repeated.minimum:
                var end = candidate + 1
                total += _match_checksum[sum_spans](end - start)
                search_start = end
        offset += CLASS_SIMD_WIDTH
    while offset < length:
        if (
            offset > search_start
            and Int(bytes[offset - 1]) == delimiter_byte
            and Int(bytes[offset]) == suffix_byte
        ):
            var delimiter_count = 0
            var start = offset
            while start > search_start and Int(bytes[start - 1]) != ord("\n"):
                start -= 1
                if Int(bytes[start]) == delimiter_byte:
                    delimiter_count += 1
            if delimiter_count >= repeated.minimum:
                var end = offset + 1
                total += _match_checksum[sum_spans](end - start)
                search_start = end
        offset += 1
    return total


@always_inline
def _count_two_delimiter_bracket_runs[
    regex: Regex, plan: _TwoDelimiterBracketRunsPlan, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Drive `A+D B+D+` matching from occurrences of the first delimiter."""
    comptime first_delimiter = regex.nodes[plan.first_delimiter_index][
        LiteralNode
    ]
    var bytes = text.as_bytes()
    var total = 0
    var next_start = 0
    var candidate = text.find(first_delimiter.value)
    while candidate >= 0:
        if candidate >= next_start:
            var start = candidate
            while start > next_start and _one_byte_atom_accepts[
                regex.nodes, plan.left_child
            ](Int(bytes[start - 1])):
                start -= 1
            if candidate - start >= plan.left_minimum:
                var end = candidate + 1
                while end < text.byte_length() and _one_byte_atom_accepts[
                    regex.nodes, plan.middle_child
                ](Int(bytes[end])):
                    end += 1
                var separator = end - 1
                while (
                    separator > candidate
                    and Int(bytes[separator]) != plan.second_byte
                ):
                    separator -= 1
                if (
                    separator > candidate + plan.middle_minimum - 1
                    and end - separator - 1 >= 1
                ):
                    total += _match_checksum[sum_spans](end - start)
                    next_start = end
                    candidate = text.find(first_delimiter.value, next_start)
                    continue
        candidate = text.find(first_delimiter.value, candidate + 1)
    return total


@always_inline
def _count_multiline_literal_edge_alternation[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Find one literal stream and test only its neighboring line bytes."""
    comptime literal_index = _multiline_literal_edge_index[
        regex.nodes, regex.root
    ]()
    comptime literal = regex.nodes[literal_index][LiteralNode]
    comptime width = literal.value.byte_length()
    var total = 0
    var next_start = 0
    var candidate = text.find(literal.value)
    var bytes = text.as_bytes()
    while candidate >= 0:
        var at_start = candidate == 0 or Int(bytes[candidate - 1]) == ord("\n")
        var end = candidate + width
        var at_end = end == text.byte_length() or Int(bytes[end]) == ord("\n")
        if candidate >= next_start and (at_start or at_end):
            total += _match_checksum[sum_spans](width)
            next_start = end
            candidate = text.find(literal.value, next_start)
        else:
            candidate = text.find(literal.value, candidate + 1)
    return total


@always_inline
def _count_end_anchored_fixed[
    regex: Regex, match_width: Int, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Evaluate a fixed-width end-anchored expression at legal starts."""
    var length = text.byte_length()
    var terminal_start = length - match_width
    var total = 0
    if length > 0 and Int(text.as_bytes()[length - 1]) == ord("\n"):
        var before_newline_start = terminal_start - 1
        if before_newline_start >= 0 and _match_node[regex.nodes, regex.root](
            text, before_newline_start
        ):
            total += _match_checksum[sum_spans](match_width)
            # The two possible fixed-width matches overlap unless their width
            # is one byte. Preserve the fallback's leftmost non-overlap order.
            if match_width != 1:
                return total
    if terminal_start >= 0 and _match_node[regex.nodes, regex.root](
        text, terminal_start
    ):
        total += _match_checksum[sum_spans](match_width)
    return total


@always_inline
def _match_simple_prefix_to[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
](text: ImmStringSpan, end: Int, minimum_start: Int) -> _MatchSpanResult:
    """Match a one-byte sequence prefix backwards with repeat giveback."""
    comptime if item < 0:
        return _MatchSpanResult(True, end, end)
    else:
        comptime node_index = sequence.items[item]
        comptime node = nodes[node_index]
        comptime if node.isa[RepeatNode]():
            comptime repeat = node[RepeatNode]
            var count = 0
            var start = end
            comptime width = CLASS_TAIL_SIMD_WIDTH
            if end - minimum_start < width + 8:
                while start > minimum_start:
                    comptime if repeat.maximum >= 0:
                        if count >= repeat.maximum:
                            break
                    if not _one_byte_atom_accepts[nodes, repeat.child](
                        Int(text.as_bytes()[start - 1])
                    ):
                        break
                    start -= 1
                    count += 1
            else:
                # Probe before paying SIMD setup; common short runs retain the
                # original scalar loop above.
                while start > minimum_start and count < 8:
                    comptime if repeat.maximum >= 0:
                        if count >= repeat.maximum:
                            break
                    if not _one_byte_atom_accepts[nodes, repeat.child](
                        Int(text.as_bytes()[start - 1])
                    ):
                        break
                    start -= 1
                    count += 1

                if count == 8:
                    while start - width >= minimum_start:
                        comptime if repeat.maximum >= 0:
                            if count + width > repeat.maximum:
                                break
                        if not all(
                            _fixed_node_mask[nodes, repeat.child, width, 0](
                                text, start - width
                            )
                        ):
                            break
                        start -= width
                        count += width

                    while start > minimum_start:
                        comptime if repeat.maximum >= 0:
                            if count >= repeat.maximum:
                                break
                        if not _one_byte_atom_accepts[nodes, repeat.child](
                            Int(text.as_bytes()[start - 1])
                        ):
                            break
                        start -= 1
                        count += 1

            while count >= repeat.minimum:
                var prefix = _match_simple_prefix_to[nodes, sequence, item - 1](
                    text, start, minimum_start
                )
                if prefix.matched:
                    return prefix^
                start += 1
                count -= 1
            return _MatchSpanResult(False, 0, 0)
        elif _is_one_byte_class_node[nodes, node_index]():
            if end <= minimum_start or not _one_byte_atom_accepts[
                nodes, node_index
            ](Int(text.as_bytes()[end - 1])):
                return _MatchSpanResult(False, 0, 0)
            return _match_simple_prefix_to[nodes, sequence, item - 1](
                text, end - 1, minimum_start
            )
        elif node.isa[LiteralNode]():
            comptime literal = node[LiteralNode]
            comptime width = literal.value.byte_length()
            var start = end - width
            if start < minimum_start or not _match_literal[literal.value](
                text, start
            ):
                return _MatchSpanResult(False, 0, 0)
            return _match_simple_prefix_to[nodes, sequence, item - 1](
                text, start, minimum_start
            )
        elif node.isa[ZeroWidthNode]():
            if not _zero_width_matches(node[ZeroWidthNode].kind, text, end):
                return _MatchSpanResult(False, 0, 0)
            return _match_simple_prefix_to[nodes, sequence, item - 1](
                text, end, minimum_start
            )
        else:
            return _match_simple_prefix_to[nodes, sequence, item - 1](
                text, end, minimum_start
            )


@always_inline
def _simple_anchor_is_disjoint[
    nodes: List[RegexNode], sequence: SequenceNode, literal_item: Int
]() -> Bool:
    """Prove a greedy prefix repeat cannot consume the anchor's first byte."""
    comptime if literal_item == 0:
        return True
    else:
        comptime previous = nodes[sequence.items[literal_item - 1]]
        comptime if not previous.isa[RepeatNode]():
            return True
        else:
            comptime repeat = previous[RepeatNode]
            comptime literal = nodes[sequence.items[literal_item]][LiteralNode]
            return not _one_byte_atom_accepts[nodes, repeat.child](
                Int(literal.value.as_bytes()[0])
            )


@always_inline
def _match_simple_infix_at[
    regex: Regex, literal_item: Int
](text: ImmStringSpan, candidate: Int, minimum_start: Int) -> _MatchSpanResult:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    var prefix = _match_simple_prefix_to[
        regex.nodes, sequence, literal_item - 1
    ](text, candidate, minimum_start)
    if not prefix.matched:
        return _MatchSpanResult(False, 0, 0)
    comptime if _simple_anchor_is_disjoint[
        regex.nodes, sequence, literal_item
    ]():
        var suffix = _match_sequence_from[regex.nodes, sequence, literal_item](
            text, candidate
        )
        if not suffix:
            return _MatchSpanResult(False, 0, 0)
        return _MatchSpanResult(
            True, prefix.start, candidate + suffix.unsafe_value().consumed()
        )
    # The prefix can greedily cross an earlier occurrence of the required
    # literal. Re-evaluate from the discovered leftmost start so forward
    # greedy semantics choose the correct occurrence and total span.
    var result = _match_node[regex.nodes, regex.root](text, prefix.start)
    if not result:
        return _MatchSpanResult(False, 0, 0)
    return _MatchSpanResult(
        True, prefix.start, prefix.start + result.unsafe_value().consumed()
    )


@always_inline
def _count_simple_infix[
    regex: Regex, literal_item: Int, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime literal = regex.nodes[sequence.items[literal_item]][LiteralNode]
    var total = 0
    var minimum_start = 0
    var candidate = text.find(literal.value)
    while candidate >= 0:
        var result = _match_simple_infix_at[regex, literal_item](
            text, candidate, minimum_start
        )
        if result.matched:
            total += _match_checksum[sum_spans](result.end - result.start)
            minimum_start = max(result.end, result.start + 1)
            candidate = text.find(literal.value, minimum_start)
        else:
            candidate = text.find(literal.value, candidate + 1)
    return total


@no_inline
def _count_greedy_run_literal_suffix[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count a greedy unbounded byte run followed by an accepted literal."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime repeat = regex.nodes[sequence.items[0]][RepeatNode]
    comptime literal = regex.nodes[sequence.items[1]][LiteralNode]
    comptime literal_length = literal.value.byte_length()
    var total = 0
    var length = text.byte_length()
    var bytes = text.as_bytes()
    var candidate = text.find(literal.value)
    while candidate >= 0:
        var run_start = candidate
        while run_start > 0 and _one_byte_atom_accepts[
            regex.nodes, repeat.child
        ](Int(bytes[run_start - 1])):
            run_start -= 1

        var run_end = candidate + literal_length
        while run_end < length and _one_byte_atom_accepts[
            regex.nodes, repeat.child
        ](Int(bytes[run_end])):
            run_end += 1

        var last = -1
        while candidate >= 0 and candidate + literal_length <= run_end:
            if candidate - run_start >= repeat.minimum:
                last = candidate
            candidate = text.find(literal.value, candidate + 1)
        if last >= 0:
            total += _match_checksum[sum_spans](
                last + literal_length - run_start
            )
    return total


@always_inline
def _search_simple_infix[
    regex: Regex, literal_item: Int
](text: ImmStringSpan) -> Bool:
    """Search a simple byte sequence from occurrences of its best literal."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime literal = regex.nodes[sequence.items[literal_item]][LiteralNode]
    var candidate = text.find(literal.value)
    while candidate >= 0:
        if _match_simple_infix_at[regex, literal_item](
            text, candidate, 0
        ).matched:
            return True
        candidate = text.find(literal.value, candidate + 1)
    return False


@always_inline
def _match_simple_class_anchor_at[
    regex: Regex, class_item: Int
](text: ImmStringSpan, candidate: Int, minimum_start: Int) -> _MatchSpanResult:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    var prefix = _match_simple_prefix_to[regex.nodes, sequence, class_item - 1](
        text, candidate, minimum_start
    )
    if not prefix.matched:
        return _MatchSpanResult(False, 0, 0)
    var result = _match_node[regex.nodes, regex.root](text, prefix.start)
    if not result:
        return _MatchSpanResult(False, 0, 0)
    return _MatchSpanResult(
        True, prefix.start, prefix.start + result.unsafe_value().consumed()
    )


@always_inline
def _search_simple_class_anchor[
    regex: Regex, class_item: Int
](text: ImmStringSpan) -> Bool:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime class_index = sequence.items[class_item]

    @always_inline
    def scan[width: Int](start: Int, end: Int) {imm text} -> Bool:
        comptime if width == 0:
            for candidate in range(start, end):
                if (
                    _node_start_accepts[regex.nodes, class_index](
                        Int(text.as_bytes()[candidate])
                    )
                    and _match_simple_class_anchor_at[regex, class_item](
                        text, candidate, 0
                    ).matched
                ):
                    return True
            return False
        else:
            var values = text.unsafe_ptr().unsafe_load[
                width=width, alignment=1
            ](start)
            var pending = pack_bits(
                _node_start_mask[regex.nodes, class_index, width](values)
            )
            while pending != 0:
                var lane = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                if _match_simple_class_anchor_at[regex, class_item](
                    text, start + lane, 0
                ).matched:
                    return True
            return False

    return _search_simd_width_ladder(text.byte_length(), 0, scan)


@always_inline
def _count_simple_class_anchor[
    regex: Regex, class_item: Int, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime class_index = sequence.items[class_item]
    var total = 0
    var next_start = 0

    @always_inline
    def scan[
        width: Int
    ](block_start: Int) {imm text, mut total, mut next_start} -> Bool:
        var values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
            block_start
        )
        var pending = pack_bits(
            _node_start_mask[regex.nodes, class_index, width](values)
        )
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var candidate = block_start + lane
            if candidate >= next_start:
                var result = _match_simple_class_anchor_at[regex, class_item](
                    text, candidate, next_start
                )
                if result.matched:
                    total += _match_checksum[sum_spans](
                        result.end - result.start
                    )
                    next_start = max(result.end, result.start + 1)
        return False

    var offset = 0
    _ = _consume_simd_width_ladder(text.byte_length(), offset, scan)
    while offset < text.byte_length():
        if offset >= next_start and _node_start_accepts[
            regex.nodes, class_index
        ](Int(text.as_bytes()[offset])):
            var result = _match_simple_class_anchor_at[regex, class_item](
                text, offset, next_start
            )
            if result.matched:
                total += _match_checksum[sum_spans](result.end - result.start)
                next_start = max(result.end, result.start + 1)
        offset += 1
    return total


@always_inline
def _count_reverse_suffix_class[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Use a required final class to evaluate a variable-width sequence."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime prefix_index = sequence.items[0]
    comptime literal = regex.nodes[sequence.items[1]][LiteralNode]
    comptime repeat = regex.nodes[sequence.items[2]][RepeatNode]
    comptime suffix_index = sequence.items[3]
    var bytes = text.as_bytes()
    var total = 0
    var minimum_start = 0
    for suffix in range(text.byte_length()):
        if not _one_byte_atom_accepts[regex.nodes, suffix_index](
            Int(bytes[suffix])
        ):
            continue
        var matched_start = -1
        var literal_start = suffix - literal.value.byte_length()
        while literal_start > minimum_start:
            var start = literal_start - 1
            var gap_start = literal_start + literal.value.byte_length()
            var gap_valid = suffix - gap_start >= repeat.minimum
            var offset = gap_start
            while gap_valid and offset < suffix:
                if not _one_byte_atom_accepts[regex.nodes, repeat.child](
                    Int(bytes[offset])
                ):
                    gap_valid = False
                offset += 1
            if (
                gap_valid
                and _match_literal[literal.value](text, literal_start)
                and _one_byte_atom_accepts[regex.nodes, prefix_index](
                    Int(bytes[start])
                )
            ):
                matched_start = start
            literal_start -= 1
        if matched_start >= minimum_start:
            total += _match_checksum[sum_spans](suffix + 1 - matched_start)
            minimum_start = suffix + 1
    return total


@always_inline
def _use_full_fixed_alternation_mask[regex: Regex, match_width: Int]() -> Bool:
    return match_width <= 8


@always_inline
def _count_fixed_width_prefiltered[
    regex: Regex, match_width: Int, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Filter fixed-width starts by their three narrowest byte predicates."""
    comptime plan = _fixed_prefilter_plan[
        regex.nodes, regex.root, match_width
    ]()
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    while offset + CLASS_SIMD_WIDTH + match_width - 1 <= length:
        comptime full_mask = _use_full_fixed_alternation_mask[
            regex, match_width
        ]()
        var candidates: SIMD[.bool, CLASS_SIMD_WIDTH]
        comptime if full_mask:
            candidates = _fixed_node_mask[
                regex.nodes, regex.root, CLASS_SIMD_WIDTH, 0
            ](text, offset)
        else:
            candidates = _fixed_offset_mask[
                regex.nodes, regex.root, CLASS_SIMD_WIDTH, plan.first
            ](text, offset)
            comptime if plan.second >= 0:
                candidates &= _fixed_offset_mask[
                    regex.nodes, regex.root, CLASS_SIMD_WIDTH, plan.second
                ](text, offset)
            comptime if plan.third >= 0:
                candidates &= _fixed_offset_mask[
                    regex.nodes, regex.root, CLASS_SIMD_WIDTH, plan.third
                ](text, offset)
            comptime if plan.fourth >= 0:
                candidates &= _fixed_offset_mask[
                    regex.nodes, regex.root, CLASS_SIMD_WIDTH, plan.fourth
                ](text, offset)
            comptime if plan.fifth >= 0:
                candidates &= _fixed_offset_mask[
                    regex.nodes, regex.root, CLASS_SIMD_WIDTH, plan.fifth
                ](text, offset)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var start = offset + lane
            var matched = start >= next_start
            comptime if not full_mask:
                matched = matched and all(
                    _fixed_node_mask[regex.nodes, regex.root, 1, 0](text, start)
                )
            if matched:
                total += _match_checksum[sum_spans](match_width)
                next_start = start + match_width
        offset += CLASS_SIMD_WIDTH

    while offset + match_width <= length:
        if offset >= next_start and all(
            _fixed_node_mask[regex.nodes, regex.root, 1, 0](text, offset)
        ):
            total += _match_checksum[sum_spans](match_width)
            next_start = offset + match_width
        offset += 1
    return total


@always_inline
def _search_fixed_width_prefiltered[
    regex: Regex, match_width: Int
](text: ImmStringSpan) -> Bool:
    """Search fixed-width starts through their narrowest byte predicates."""
    comptime plan = _fixed_prefilter_plan[
        regex.nodes, regex.root, match_width
    ]()
    var length = text.byte_length()
    var offset = 0

    @always_inline
    def scan[width: Int](block_start: Int) {imm text} -> Bool:
        var candidates = _fixed_offset_mask[
            regex.nodes, regex.root, width, plan.first
        ](text, block_start)
        comptime if plan.second >= 0:
            candidates &= _fixed_offset_mask[
                regex.nodes, regex.root, width, plan.second
            ](text, block_start)
        comptime if plan.third >= 0:
            candidates &= _fixed_offset_mask[
                regex.nodes, regex.root, width, plan.third
            ](text, block_start)
        comptime if plan.fourth >= 0:
            candidates &= _fixed_offset_mask[
                regex.nodes, regex.root, width, plan.fourth
            ](text, block_start)
        comptime if plan.fifth >= 0:
            candidates &= _fixed_offset_mask[
                regex.nodes, regex.root, width, plan.fifth
            ](text, block_start)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            if all(
                _fixed_node_mask[regex.nodes, regex.root, 1, 0](
                    text, block_start + lane
                )
            ):
                return True
        return False

    var candidate_count = max(0, length - match_width + 1)
    if _consume_simd_width_ladder(candidate_count, offset, scan):
        return True
    while offset < candidate_count:
        if scan[1](offset):
            return True
        offset += 1
    return False


@always_inline
def _count_one_byte_atom[regex: Regex](text: ImmStringSpan) -> Int:
    """Count accepted one-byte atoms with SIMD mask population reductions."""
    var length = text.byte_length()
    var total = 0
    var offset = 0

    @always_inline
    def scan[
        width: Int
    ](block_start: Int) {imm text, mut total,} -> Bool:
        total += _fixed_node_mask[regex.nodes, regex.root, width, 0](
            text, block_start
        ).reduce_bit_count()
        return False

    _ = _consume_simd_width_ladder(length, offset, scan)

    while offset < length:
        if _one_byte_atom_accepts[regex.nodes, regex.root](
            Int(text.as_bytes()[offset])
        ):
            total += 1
        offset += 1
    return total


@always_inline
def _capitalized_word_phrase_end(text: ImmStringSpan, start: Int) -> Int:
    var length = text.byte_length()
    if start >= length:
        return -1
    var bytes = text.as_bytes()
    var value = Int(bytes[start])
    if not (ord("A") <= value <= ord("Z")):
        return -1
    var end = start + 1
    if end >= length:
        return -1
    value = Int(bytes[end])
    if not (ord("a") <= value <= ord("z")):
        return -1
    end += 1
    while end < length:
        value = Int(bytes[end])
        if not (ord("a") <= value <= ord("z")):
            break
        end += 1
    while end < length and _accepts_class[CHAR_ASCII_WHITESPACE](
        Int(bytes[end])
    ):
        end += 1
    return end


@always_inline
def _next_ascii_uppercase(text: ImmStringSpan, start: Int) -> Int:
    """Find the next ASCII uppercase byte with native-width SIMD."""
    var length = text.byte_length()
    var offset = start
    var pointer = text.unsafe_ptr()
    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while offset + width <= length:
            var values = pointer.unsafe_load[width=width, alignment=1](offset)
            var candidates = _byte_range_mask[ord("A"), ord("Z"), width](values)
            var pending = pack_bits(candidates)
            if pending != 0:
                return offset + Int(count_trailing_zeros(pending))
            offset += width
    var bytes = text.as_bytes()
    while offset < length:
        var value = Int(bytes[offset])
        if ord("A") <= value <= ord("Z"):
            return offset
        offset += 1
    return -1


@always_inline
def _count_bounded_capitalized_word_sequence[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count capitalized phrase runs once instead of retrying nested repeats."""
    comptime outer = regex.nodes[regex.root][RepeatNode]
    comptime minimum = outer.minimum
    comptime maximum = outer.maximum
    var total = 0
    var offset = 0
    var length = text.byte_length()
    while offset < length:
        offset = _next_ascii_uppercase(text, offset)
        if offset < 0:
            break
        var phrase_end = _capitalized_word_phrase_end(text, offset)
        if phrase_end < 0:
            offset += 1
            continue
        var match_start = offset
        var phrases = 0
        while phrase_end >= 0:
            phrases += 1
            offset = phrase_end
            if phrases == maximum:
                total += _match_checksum[sum_spans](offset - match_start)
                phrases = 0
                match_start = offset
            phrase_end = _capitalized_word_phrase_end(text, offset)
        if phrases >= minimum:
            total += _match_checksum[sum_spans](offset - match_start)
    return total


@always_inline
def _contains_one_byte_node[
    nodes: List[RegexNode], node_index: Int
](text: ImmStringSpan) -> Bool:
    """Return whether a byte class occurs, using the native SIMD width."""
    var length = text.byte_length()
    var offset = 0

    @always_inline
    def scan[width: Int](block_start: Int) {imm text} -> Bool:
        return any(
            _fixed_node_mask[nodes, node_index, width, 0](text, block_start)
        )

    if _consume_simd_width_ladder(length, offset, scan):
        return True

    while offset < length:
        if _one_byte_atom_accepts[nodes, node_index](
            Int(text.as_bytes()[offset])
        ):
            return True
        offset += 1
    return False


@always_inline
def _bounded_class_run_checksum[
    minimum: Int, maximum: Int, greedy: Bool, sum_spans: Bool
](run_length: Int) -> Int:
    comptime if maximum < 0:
        if run_length < minimum:
            return 0
        comptime if greedy:
            comptime if sum_spans:
                return run_length
            return 1
        else:
            var matches = run_length // minimum
            comptime if sum_spans:
                return matches * minimum
            return matches
    elif greedy:
        var full_matches = run_length // maximum
        var remainder = run_length - full_matches * maximum
        comptime if sum_spans:
            if remainder >= minimum:
                return full_matches * maximum + remainder
            return full_matches * maximum
        else:
            return full_matches + Int(remainder >= minimum)
    else:
        var matches = run_length // minimum
        comptime if sum_spans:
            return matches * minimum
        else:
            return matches


@always_inline
def _count_one_byte_class_repeat[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """SIMD-classify bytes and consume each maximal accepted run once."""
    comptime repeat = regex.nodes[regex.root][RepeatNode]
    comptime minimum = repeat.minimum
    comptime maximum = repeat.maximum
    var length = text.byte_length()
    if length < minimum:
        return 0
    var total = 0
    var run_length = 0
    var offset = 0
    while offset + CLASS_SIMD_WIDTH <= length:
        var accepted = _fixed_node_mask[
            regex.nodes, repeat.child, CLASS_SIMD_WIDTH, 0
        ](text, offset)
        var rejected = pack_bits(
            accepted ^ SIMD[.bool, CLASS_SIMD_WIDTH](fill=True)
        )
        var block_position = 0
        while rejected != 0:
            var lane = Int(count_trailing_zeros(rejected))
            run_length += lane - block_position
            total += _bounded_class_run_checksum[
                minimum, maximum, repeat.greedy, sum_spans
            ](run_length)
            run_length = 0
            block_position = lane + 1
            rejected &= rejected - 1
        run_length += CLASS_SIMD_WIDTH - block_position
        offset += CLASS_SIMD_WIDTH

    var bytes = text.as_bytes()
    while offset < length:
        if _bounded_repeat_byte_accepts[regex.nodes, repeat.child](
            Int(bytes[offset])
        ):
            run_length += 1
        else:
            total += _bounded_class_run_checksum[
                minimum, maximum, repeat.greedy, sum_spans
            ](run_length)
            run_length = 0
        offset += 1
    return total + _bounded_class_run_checksum[
        minimum, maximum, repeat.greedy, sum_spans
    ](run_length)


@always_inline
def _search_one_byte_run[
    nodes: List[RegexNode], child: Int, minimum: Int
](text: ImmStringSpan) -> Bool:
    """Search for `minimum` consecutive bytes accepted by one AST node."""
    comptime width = CLASS_TAIL_SIMD_WIDTH
    var length = text.byte_length()
    if length < minimum:
        return False

    var offset = 0
    comptime if minimum <= width:
        while offset + width + minimum - 1 <= length:
            var candidates = _fixed_node_mask[nodes, child, width, 0](
                text, offset
            )
            comptime for shift in range(1, minimum):
                candidates &= _fixed_node_mask[nodes, child, width, shift](
                    text, offset
                )
            if any(candidates):
                return True
            offset += width

    # For large minima and the tail, a rejected byte skips every candidate
    # window containing it.  This remains linear without a per-start matcher.
    var bytes = text.as_bytes()
    var window_end = offset + minimum - 1
    while window_end < length:
        var window_start = window_end - minimum + 1
        var cursor = window_end
        while cursor >= window_start:
            if not _bounded_repeat_byte_accepts[nodes, child](
                Int(bytes[cursor])
            ):
                break
            cursor -= 1
        if cursor < window_start:
            return True
        window_end = cursor + minimum
    return False


@always_inline
def _search_one_byte_class_repeat[regex: Regex](text: ImmStringSpan) -> Bool:
    """Search a root byte-predicate repeat by complete runs, not starts."""
    comptime repeat = regex.nodes[regex.root][RepeatNode]
    return _search_one_byte_run[regex.nodes, repeat.child, repeat.minimum](text)


@always_inline
def _count_nested_run_then_disjoint_class[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count `(class+)*other_class` as the equivalent `class*other_class`."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime outer = regex.nodes[sequence.items[0]][RepeatNode]
    comptime inner = regex.nodes[outer.child][RepeatNode]
    comptime suffix_index = sequence.items[1]
    if not _contains_one_byte_node[regex.nodes, suffix_index](text):
        return 0

    var total = 0
    var run_length = 0
    var bytes = text.as_bytes()
    for position in range(text.byte_length()):
        var value = Int(bytes[position])
        if _one_byte_atom_accepts[regex.nodes, inner.child](value):
            run_length += 1
        elif _one_byte_atom_accepts[regex.nodes, suffix_index](value):
            total += _match_checksum[sum_spans](run_length + 1)
            run_length = 0
        else:
            run_length = 0
    return total


@always_inline
def _bounded_prefix_length_before[
    regex: Regex
](text: ImmStringSpan, suffix_start: Int, minimum_start: Int) -> Int:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime repeat = regex.nodes[sequence.items[0]][RepeatNode]
    var available = min(repeat.maximum, suffix_start - minimum_start)
    var prefix_length = 0
    var bytes = text.as_bytes()
    while prefix_length < available:
        var position = suffix_start - prefix_length - 1
        if not _one_byte_atom_accepts[regex.nodes, repeat.child](
            Int(bytes[position])
        ):
            break
        prefix_length += 1
    if prefix_length < repeat.minimum:
        return -1
    return prefix_length


@always_inline
def _count_bounded_prefix_literal_alternation[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """SIMD-scan mandatory alternatives, then test the bounded prefix."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime alternation = regex.nodes[sequence.items[1]][OrNode]
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    var pointer = text.unsafe_ptr()
    while offset + CLASS_SIMD_WIDTH <= length:
        if not _literal_alternation_block_fits[
            regex.nodes, alternation, CLASS_SIMD_WIDTH
        ](length, offset):
            break
        var first_values = pointer.unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](offset)
        var candidates = _literal_alternation_candidate_mask[
            regex.nodes, alternation, CLASS_SIMD_WIDTH
        ](text, offset, first_values)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var suffix_start = offset + lane
            if suffix_start >= next_start:
                var suffix_length = _literal_alternation_match_length_at[
                    regex.nodes, alternation
                ](text, suffix_start)
                if suffix_length > 0:
                    var prefix_length = _bounded_prefix_length_before[regex](
                        text, suffix_start, next_start
                    )
                    if prefix_length >= 0:
                        total += _match_checksum[sum_spans](
                            prefix_length + suffix_length
                        )
                        next_start = suffix_start + suffix_length
        offset += CLASS_SIMD_WIDTH

    while offset < length:
        if offset >= next_start:
            var suffix_length = _literal_alternation_match_length_at[
                regex.nodes, alternation
            ](text, offset)
            if suffix_length > 0:
                var prefix_length = _bounded_prefix_length_before[regex](
                    text, offset, next_start
                )
                if prefix_length >= 0:
                    total += _match_checksum[sum_spans](
                        prefix_length + suffix_length
                    )
                    next_start = offset + suffix_length
        offset += 1
    return total


def _class_literal_alternation_max_width[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    var maximum = 0
    comptime for option in range(alternation.count):
        comptime current = _fixed_node_width[
            nodes, alternation.options[option]
        ]()
        maximum = max(maximum, current)
    return maximum


def _class_literal_alternation_common_prefix[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    """Return a shared bracket prefix for every branch, or -1."""
    comptime first_option = nodes[alternation.options[0]][SequenceNode]
    comptime first_index = first_option.items[0]
    comptime first_node = nodes[first_index]
    comptime if not first_node.isa[BracketClassNode]():
        return -1
    comptime first = first_node[BracketClassNode]
    comptime for i in range(1, alternation.count):
        comptime option = nodes[alternation.options[i]][SequenceNode]
        comptime prefix_node = nodes[option.items[0]]
        comptime if not prefix_node.isa[BracketClassNode]():
            return -1
        comptime prefix = prefix_node[BracketClassNode]
        comptime if (
            first.negated != prefix.negated
            or not _same_bracket_ranges[first, prefix]()
        ):
            return -1
    return first_index


@always_inline
def _class_literal_alternation_mask[
    regex: Regex, width: Int
](text: ImmStringSpan, block_start: Int) -> SIMD[.bool, width]:
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime alternation = regex.nodes[root.items[0]][OrNode]
    comptime suffix = root.items[1]
    comptime common_prefix = _class_literal_alternation_common_prefix[
        regex.nodes, alternation
    ]()
    comptime if common_prefix >= 0:
        comptime common_node = regex.nodes[common_prefix]
        comptime if common_node.isa[BracketClassNode]():
            comptime common = common_node[BracketClassNode]
            comptime if _is_exact_bracket_range[common](ord("A"), ord("Z")):
                # A selective shared uppercase prefix is cheaper than checking
                # literal edges and the final class for every branch.
                return _fixed_node_mask[regex.nodes, common_prefix, width, 0](
                    text, block_start
                )
    var matched = SIMD[.bool, width](fill=False)
    var first_values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
        block_start + 1
    )
    comptime for i in range(alternation.count):
        comptime option = regex.nodes[alternation.options[i]][SequenceNode]
        comptime literal = regex.nodes[option.items[1]][LiteralNode]
        var branch = SIMD[.bool, width](fill=True)
        comptime first = literal.value.as_bytes()[0]
        branch &= first_values.eq(SIMD[.uint8, width](first))
        comptime if literal.value.byte_length() > 1:
            var last_values = text.unsafe_ptr().unsafe_load[
                width=width, alignment=1
            ](block_start + literal.value.byte_length())
            comptime last = literal.value.as_bytes()[
                literal.value.byte_length() - 1
            ]
            branch &= last_values.eq(SIMD[.uint8, width](last))
        comptime pattern_offset = 1 + literal.value.byte_length()
        comptime suffix_node = regex.nodes[suffix]
        comptime if (
            suffix_node.isa[CharClassNode]()
            and suffix_node[CharClassNode].kind == CHAR_ASCII_WHITESPACE
        ):
            var suffix_values = text.unsafe_ptr().unsafe_load[
                width=width, alignment=1
            ](block_start + pattern_offset)
            branch &= suffix_values.le(SIMD[.uint8, width](UInt8(ord(" "))))
        else:
            branch &= _fixed_node_mask[
                regex.nodes, suffix, width, pattern_offset
            ](text, block_start)
        matched |= branch
    return matched


@always_inline
def _count_class_literal_alternation_with_suffix[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Evaluate class/literal branches together in one SIMD corpus pass."""
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime alternation = regex.nodes[root.items[0]][OrNode]
    comptime max_width = 1 + _class_literal_alternation_max_width[
        regex.nodes, alternation
    ]()
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    while offset + CLASS_SIMD_WIDTH + max_width - 1 <= length:
        var candidates = _class_literal_alternation_mask[
            regex, CLASS_SIMD_WIDTH
        ](text, offset)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var start = offset + lane
            if start >= next_start:
                var result = _match_node[regex.nodes, regex.root](text, start)
                if result:
                    var consumed = result.unsafe_value().consumed()
                    total += _match_checksum[sum_spans](consumed)
                    next_start = start + max(1, consumed)
        offset += CLASS_SIMD_WIDTH
    while offset < length:
        if offset >= next_start:
            var result = _match_node[regex.nodes, regex.root](text, offset)
            if result:
                var consumed = result.unsafe_value().consumed()
                total += _match_checksum[sum_spans](consumed)
                next_start = offset + max(1, consumed)
        offset += 1
    return total


@always_inline
def _count_symmetric_bounded_delimited[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Pair consecutive SIMD-found delimiters for `D [^D]{m,n} C D`."""
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime delimiter = regex.nodes[root.items[0]][BracketClassNode]
    comptime repeat = regex.nodes[root.items[1]][RepeatNode]
    comptime middle = root.items[2]
    var length = text.byte_length()
    var total = 0
    var previous = -1
    var offset = 0
    var pointer = text.unsafe_ptr()
    while offset + CLASS_SIMD_WIDTH <= length:
        var values = pointer.unsafe_load[width=CLASS_SIMD_WIDTH, alignment=1](
            offset
        )
        var delimiters = _bracket_mask[delimiter, CLASS_SIMD_WIDTH](values)
        if any(delimiters):
            comptime for lane in range(CLASS_SIMD_WIDTH):
                if delimiters[lane]:
                    var position = offset + lane
                    if previous >= 0:
                        var repetitions = position - previous - 2
                        if (
                            repeat.minimum <= repetitions <= repeat.maximum
                            and _one_byte_atom_accepts[regex.nodes, middle](
                                Int(text.as_bytes()[position - 1])
                            )
                        ):
                            total += _match_checksum[sum_spans](
                                position + 1 - previous
                            )
                            previous = -1
                            continue
                    previous = position
        offset += CLASS_SIMD_WIDTH
    while offset < length:
        if _bracket_accepts[delimiter](Int(text.as_bytes()[offset])):
            if previous >= 0:
                var repetitions = offset - previous - 2
                if (
                    repeat.minimum <= repetitions <= repeat.maximum
                    and _one_byte_atom_accepts[regex.nodes, middle](
                        Int(text.as_bytes()[offset - 1])
                    )
                ):
                    total += _match_checksum[sum_spans](offset + 1 - previous)
                    previous = -1
                    offset += 1
                    continue
            previous = offset
        offset += 1
    return total


@always_inline
def _count_bracket_prefixed_sequence[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Use the leading bracket class as a SIMD candidate prefilter."""
    comptime if _is_symmetric_bounded_delimited_sequence[
        regex.nodes, regex.root
    ]():
        return _count_symmetric_bounded_delimited[regex, sum_spans](text)
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime prefix = regex.nodes[root.items[0]][BracketClassNode]
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    var pointer = text.unsafe_ptr()
    while offset + CLASS_SIMD_WIDTH <= length:
        var values = pointer.unsafe_load[width=CLASS_SIMD_WIDTH, alignment=1](
            offset
        )
        var candidates = _bracket_mask[prefix, CLASS_SIMD_WIDTH](values)
        if any(candidates):
            comptime for lane in range(CLASS_SIMD_WIDTH):
                var start = offset + lane
                if start >= next_start and candidates[lane]:
                    var result = _match_node[regex.nodes, regex.root](
                        text, start
                    )
                    if result:
                        var consumed = result.unsafe_value().consumed()
                        total += _match_checksum[sum_spans](consumed)
                        next_start = start + max(1, consumed)
        offset += CLASS_SIMD_WIDTH
    while offset < length:
        if offset >= next_start and _bracket_accepts[prefix](
            Int(text.as_bytes()[offset])
        ):
            var result = _match_node[regex.nodes, regex.root](text, offset)
            if result:
                var consumed = result.unsafe_value().consumed()
                total += _match_checksum[sum_spans](consumed)
                next_start = offset + max(1, consumed)
        offset += 1
    return total


@always_inline
def _bounded_line_gap_alternation_match_length[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Int:
    """Match a normalized bounded content-line gap from one literal prefix."""
    comptime alternation = regex.nodes[regex.root][OrNode]
    comptime for option in range(alternation.count):
        comptime sequence = regex.nodes[alternation.options[option]][
            SequenceNode
        ]
        comptime prefix = regex.nodes[sequence.items[0]][LiteralNode]
        if not _match_literal[prefix.value](text, start):
            continue
        comptime gap = regex.nodes[sequence.items[1]][RepeatNode]
        comptime suffix = regex.nodes[sequence.items[2]][LiteralNode]
        var position = start + prefix.value.byte_length()
        var content_lines = 0
        var limit = text.byte_length()
        var bytes = text.as_bytes()
        var line_start = position
        while line_start < text.byte_length():
            var newline = text.find("\n", line_start)
            var line_end = text.byte_length() if newline < 0 else newline
            var content = line_start
            while content < line_end and _accepts_class[CHAR_ASCII_WHITESPACE](
                Int(bytes[content])
            ):
                content += 1
            if content < line_end:
                if content_lines >= gap.maximum:
                    # The suffix is tested before the dot-repeat attempts to
                    # consume this first byte, so include this position.
                    limit = content
                    break
                content_lines += 1
            if newline < 0:
                break
            line_start = newline + 1

        var candidate = text.find(suffix.value, position)
        var best_end = -1
        while candidate >= 0 and candidate <= limit:
            best_end = candidate + suffix.value.byte_length()
            candidate = text.find(suffix.value, candidate + 1)
        if best_end >= 0:
            return best_end - start
    return -1


@always_inline
def _prefixed_alternation_match_length[
    regex: Regex, use_nfa: Bool = False
](text: ImmStringSpan, start: Int) -> Int:
    comptime if _is_bounded_line_gap_literal_alternation[
        regex.nodes, regex.root
    ]():
        return _bounded_line_gap_alternation_match_length[regex](text, start)
    comptime if use_nfa:
        var result = _nfa_match_at[regex](text, start)
        return result.unsafe_value().consumed if result else -1
    else:
        var result = _match_node[regex.nodes, regex.root](text, start)
        return result.unsafe_value().consumed() if result else -1


@always_inline
def _prefixed_alternation_literal_matches_at[
    nodes: List[RegexNode], alternation: OrNode
](text: ImmStringSpan, start: Int) -> Bool:
    """Confirm a complete mandatory branch prefix at a SIMD candidate."""
    comptime for option in range(alternation.count):
        comptime prefix_index = _sequence_prefix_literal_index[
            nodes, alternation.options[option]
        ]()
        comptime prefix = nodes[prefix_index][LiteralNode]
        if _match_literal[prefix.value](text, start):
            return True
    return False


@always_inline
def _count_prefixed_alternation_simd[
    regex: Regex,
    alternation: OrNode,
    sum_spans: Bool,
    use_nfa: Bool = False,
](text: ImmStringSpan) -> Int:
    """Scan correlated literal-prefix bytes once for every branch."""
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0

    @always_inline
    def scan[
        width: Int
    ](block_start: Int) {imm text, mut total, mut next_start} -> Bool:
        var pointer = text.unsafe_ptr()
        var first_values = pointer.unsafe_load[width=width, alignment=1](
            block_start
        )
        var third_values = pointer.unsafe_load[width=width, alignment=1](
            block_start + 2
        )
        var candidates = _alternation_two_position_mask[
            regex.nodes, alternation, 0, 2, True, width
        ](first_values, third_values)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var start = block_start + lane
            if start >= next_start:
                comptime if use_nfa:
                    if not _prefixed_alternation_literal_matches_at[
                        regex.nodes, alternation
                    ](text, start):
                        continue
                var consumed = _prefixed_alternation_match_length[
                    regex, use_nfa
                ](text, start)
                if consumed >= 0:
                    total += _match_checksum[sum_spans](consumed)
                    next_start = start + max(1, consumed)
        return False

    var limit = max(0, length - 2)
    _ = _consume_simd_width_ladder(limit, offset, scan)
    var bytes = text.as_bytes()
    while offset < limit:
        var candidate = False
        comptime for i in range(alternation.count):
            comptime prefix_index = _sequence_prefix_literal_index[
                regex.nodes, alternation.options[i]
            ]()
            comptime prefix = regex.nodes[prefix_index][LiteralNode].value
            candidate |= (
                bytes[offset] == prefix.as_bytes()[0]
                and bytes[offset + 2] == prefix.as_bytes()[2]
            )
        if offset >= next_start and candidate:
            comptime if use_nfa:
                if not _prefixed_alternation_literal_matches_at[
                    regex.nodes, alternation
                ](text, offset):
                    offset += 1
                    continue
            var consumed = _prefixed_alternation_match_length[regex, use_nfa](
                text, offset
            )
            if consumed >= 0:
                total += _match_checksum[sum_spans](consumed)
                next_start = offset + max(1, consumed)
        offset += 1
    return total


@always_inline
def _count_prefixed_alternation[
    regex: Regex, alternation: OrNode, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Merge persistent mandatory-prefix cursors in leftmost order."""
    comptime if _all_prefixed_sequence_options[regex.nodes, alternation, 3]():
        return _count_prefixed_alternation_simd[regex, alternation, sum_spans](
            text
        )
    var total = 0
    var search_start: Int
    var candidates = StaticTuple[Int, MAX_BRANCHES]()
    comptime for i in range(alternation.count):
        comptime prefix_index = _sequence_prefix_literal_index[
            regex.nodes, alternation.options[i]
        ]()
        comptime prefix = regex.nodes[prefix_index][LiteralNode]
        candidates[i] = text.find(prefix.value)

    while True:
        var candidate = -1
        comptime for i in range(alternation.count):
            if candidates[i] >= 0 and (
                candidate < 0 or candidates[i] < candidate
            ):
                candidate = candidates[i]
        if candidate < 0:
            break
        var consumed = _prefixed_alternation_match_length[regex](
            text, candidate
        )
        if consumed >= 0:
            total += _match_checksum[sum_spans](consumed)
            search_start = candidate + max(1, consumed)
        else:
            search_start = candidate + 1
        comptime for i in range(alternation.count):
            if candidates[i] < search_start:
                comptime prefix_index = _sequence_prefix_literal_index[
                    regex.nodes, alternation.options[i]
                ]()
                comptime prefix = regex.nodes[prefix_index][LiteralNode]
                candidates[i] = text.find(prefix.value, search_start)
    return total
