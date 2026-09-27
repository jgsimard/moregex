"""Bounded and prefixed-alternation aggregation kernels."""

from ._simd import _consume_simd_width_ladder
from ._width import _fixed_node_width
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
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits
from std.utils import StaticTuple

from ._ast_equal import _same_bracket_ranges
from ._common import (
    CLASS_SIMD_WIDTH,
    _accepts_class,
    _bracket_accepts,
    _match_checksum,
    _match_literal,
)

from ._analysis import (
    _all_prefixed_sequence_options,
    _bracket_mask,
    _fixed_node_mask,
    _is_bounded_line_gap_literal_alternation,
    _is_exact_bracket_range,
    _is_symmetric_bounded_delimited_sequence,
    _one_byte_atom_accepts,
    _sequence_prefix_literal_index,
)


from ._ast_matcher import (
    _match_node,
)
from ._nfa import _nfa_match_at


from ._literals import (
    _alternation_two_position_mask,
    _literal_alternation_block_fits,
    _literal_alternation_candidate_mask,
    _literal_alternation_match_length_at,
)


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
            or not _same_bracket_ranges(first, prefix)
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
        return result.unsafe_value().consumed() if result else -1
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
