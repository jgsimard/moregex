"""Fixed-width, anchor, and infix aggregation kernels."""

from ._simd import _consume_simd_width_ladder, _search_simd_width_ladder
from ._ast import (
    LiteralNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits

from ._common import (
    CLASS_SIMD_WIDTH,
    CLASS_TAIL_SIMD_WIDTH,
    _match_checksum,
    _match_literal,
    _zero_width_matches,
)

from ._analysis import (
    _fixed_node_mask,
    _fixed_offset_mask,
    _fixed_prefilter_plan,
    _is_one_byte_class_node,
    _node_start_accepts,
    _node_start_mask,
    _one_byte_atom_accepts,
)


from ._result import _MatchSpan
from ._ast_matcher import (
    _match_sequence_from,
    _match_node,
)


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
](text: ImmStringSpan, end: Int, minimum_start: Int) -> Optional[_MatchSpan]:
    """Match a one-byte sequence prefix backwards with repeat giveback."""
    comptime if item < 0:
        return _MatchSpan(end, end)
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
                if prefix:
                    return prefix^
                start += 1
                count -= 1
            return None
        elif _is_one_byte_class_node[nodes, node_index]():
            if end <= minimum_start or not _one_byte_atom_accepts[
                nodes, node_index
            ](Int(text.as_bytes()[end - 1])):
                return None
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
                return None
            return _match_simple_prefix_to[nodes, sequence, item - 1](
                text, start, minimum_start
            )
        elif node.isa[ZeroWidthNode]():
            if not _zero_width_matches(node[ZeroWidthNode].kind, text, end):
                return None
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
](text: ImmStringSpan, candidate: Int, minimum_start: Int) -> Optional[
    _MatchSpan
]:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    var prefix = _match_simple_prefix_to[
        regex.nodes, sequence, literal_item - 1
    ](text, candidate, minimum_start)
    if not prefix:
        return None
    comptime if _simple_anchor_is_disjoint[
        regex.nodes, sequence, literal_item
    ]():
        var suffix = _match_sequence_from[regex.nodes, sequence, literal_item](
            text, candidate
        )
        if not suffix:
            return None
        var span = prefix.unsafe_value()
        return _MatchSpan(
            span.start, candidate + suffix.unsafe_value().consumed()
        )
    # The prefix can greedily cross an earlier occurrence of the required
    # literal. Re-evaluate from the discovered leftmost start so forward
    # greedy semantics choose the correct occurrence and total span.
    var span = prefix.unsafe_value()
    var result = _match_node[regex.nodes, regex.root](text, span.start)
    if not result:
        return None
    return _MatchSpan(span.start, span.start + result.unsafe_value().consumed())


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
        if result:
            var span = result.unsafe_value()
            total += _match_checksum[sum_spans](span.consumed())
            minimum_start = max(span.end, span.start + 1)
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
        if _match_simple_infix_at[regex, literal_item](text, candidate, 0):
            return True
        candidate = text.find(literal.value, candidate + 1)
    return False


@always_inline
def _match_simple_class_anchor_at[
    regex: Regex, class_item: Int
](text: ImmStringSpan, candidate: Int, minimum_start: Int) -> Optional[
    _MatchSpan
]:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    var prefix = _match_simple_prefix_to[regex.nodes, sequence, class_item - 1](
        text, candidate, minimum_start
    )
    if not prefix:
        return None
    var span = prefix.unsafe_value()
    var result = _match_node[regex.nodes, regex.root](text, span.start)
    if not result:
        return None
    return _MatchSpan(span.start, span.start + result.unsafe_value().consumed())


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
                if _node_start_accepts[regex.nodes, class_index](
                    Int(text.as_bytes()[candidate])
                ) and _match_simple_class_anchor_at[regex, class_item](
                    text, candidate, 0
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
                ):
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
                if result:
                    var span = result.unsafe_value()
                    total += _match_checksum[sum_spans](span.consumed())
                    next_start = max(span.end, span.start + 1)
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
            if result:
                var span = result.unsafe_value()
                total += _match_checksum[sum_spans](span.consumed())
                next_start = max(span.end, span.start + 1)
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
