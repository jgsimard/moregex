"""Specialized regex count kernels."""

from ._ast import (
    BracketClassNode,
    LiteralNode,
    OrNode,
    RepeatNode,
    SequenceNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits

from ._common import (
    CLASS_SIMD_WIDTH,
    CLASS_TAIL_SIMD_WIDTH,
    _bracket_accepts,
    _match_checksum,
    _match_literal,
)

from ._analysis import (
    _TwoDelimiterBracketRunsPlan,
    _bracket_mask,
    _is_end_assertion_node,
    _multiline_literal_edge_index,
    _one_byte_atom_accepts,
)


from ._ast_matcher import (
    _match_node,
)


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
