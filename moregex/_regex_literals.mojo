"""Specialized literal-alternation kernels."""

from ._ast import (
    BracketClassNode,
    LiteralNode,
    MAX_BRANCHES,
    OrNode,
    RegexNode,
    SequenceNode,
)
from std.bit import count_trailing_zeros
from std.memory import pack_bits
from std.sys import CompilationTarget, llvm_intrinsic, simd_width_of
from std.utils import StaticTuple

from ._regex_common import (
    CLASS_SIMD_WIDTH,
    _match_checksum,
    _match_literal,
)

from ._regex_analysis import (
    _all_literal_options,
    _literal_alternation_same_first_byte,
    _sequence_prefix_literal_index,
)


@always_inline
def _literal_alternation_matches_at[
    nodes: List[RegexNode], alternation: OrNode
](text: ImmStringSpan, start: Int) -> Bool:
    comptime for i in range(alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        comptime first = Int(literal.value.as_bytes()[0])
        if Int(text.as_bytes()[start]) == first:
            if _match_literal[literal.value](text, start):
                return True
    return False


@always_inline
def _literal_alternation_max_width[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    var maximum = 0
    comptime for option in range(alternation.count):
        comptime literal = nodes[alternation.options[option]][LiteralNode]
        maximum = max(maximum, literal.value.byte_length())
    return maximum


@always_inline
def _literal_alternation_block_fits[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](length: Int, offset: Int) -> Bool:
    comptime maximum = _literal_alternation_max_width[nodes, alternation]()
    return offset + width + maximum - 1 <= length


@always_inline
def _literal_alternation_block_matches[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](text: ImmStringSpan, offset: Int, first_values: SIMD[.uint8, width]) -> Bool:
    # _literal_alternation_block_fits proves every shifted vector load below is
    # in bounds for every compile-time branch.
    var pointer = text.unsafe_ptr()
    comptime for i in range(alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        comptime first = literal.value.as_bytes()[0]
        var branch = first_values.eq(first)
        if any(branch):
            comptime for position in range(1, literal.value.byte_length()):
                var values = pointer.unsafe_load[width=width, alignment=1](
                    offset + position
                )
                comptime expected = literal.value.as_bytes()[position]
                branch &= values.eq(expected)
            if any(branch):
                return True
    return False


@always_inline
def _literal_alternation_full_mask[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](text: ImmStringSpan, offset: Int, first_values: SIMD[.uint8, width]) -> SIMD[
    .bool, width
]:
    """Return starts where any literal alternative matches completely."""
    var matched = SIMD[.bool, width](fill=False)
    var pointer = text.unsafe_ptr()
    comptime for i in range(alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        comptime first = literal.value.as_bytes()[0]
        var branch = first_values.eq(first)
        comptime for position in range(1, literal.value.byte_length()):
            var values = pointer.unsafe_load[width=width, alignment=1](
                offset + position
            )
            comptime expected = literal.value.as_bytes()[position]
            branch &= values.eq(expected)
        matched |= branch
    return matched


@always_inline
def _alternation_two_position_mask[
    nodes: List[RegexNode],
    alternation: OrNode,
    first_position: Int,
    second_position: Int,
    prefixed: Bool,
    width: Int,
](
    first_values: SIMD[.uint8, width],
    second_values: SIMD[.uint8, width],
) -> SIMD[.bool, width]:
    """Filter alternatives using two selected literal positions."""
    var matched = SIMD[.bool, width](fill=False)
    comptime for i in range(alternation.count):
        comptime first = _alternation_byte[
            nodes, alternation, first_position, prefixed, False, i
        ]()
        comptime second = _alternation_byte[
            nodes, alternation, second_position, prefixed, False, i
        ]()
        matched |= first_values.eq(first) & second_values.eq(second)
    return matched


@always_inline
def _literal_alternation_three_byte_mask[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](
    first_values: SIMD[.uint8, width],
    second_values: SIMD[.uint8, width],
    third_values: SIMD[.uint8, width],
) -> SIMD[.bool, width]:
    """Filter larger literal sets using exact three-byte prefixes."""
    var matched = SIMD[.bool, width](fill=False)
    comptime for i in range(alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        comptime first = literal.value.as_bytes()[0]
        comptime second = literal.value.as_bytes()[1]
        comptime third = literal.value.as_bytes()[2]
        matched |= (
            first_values.eq(first)
            & second_values.eq(second)
            & third_values.eq(third)
        )
    return matched


def _alternation_byte[
    nodes: List[RegexNode],
    alternation: OrNode,
    position: Int,
    prefixed: Bool,
    casefold: Bool,
    option: Int,
]() -> UInt8:
    comptime if prefixed:
        comptime literal_index = _sequence_prefix_literal_index[
            nodes, alternation.options[option]
        ]()
        comptime literal = nodes[literal_index][LiteralNode]
        return literal.value.as_bytes()[position]
    elif casefold:
        comptime sequence = nodes[alternation.options[option]][SequenceNode]
        comptime letter = nodes[sequence.items[position]][BracketClassNode]
        return UInt8(letter.lows[0] | 0x20)
    else:
        comptime literal = nodes[alternation.options[option]][LiteralNode]
        return literal.value.as_bytes()[position]


@always_inline
def _alternation_nibble_table[
    nodes: List[RegexNode],
    alternation: OrNode,
    position: Int,
    casefold: Bool,
    high: Bool,
    width: Int,
]() -> SIMD[.uint8, width]:
    var table = SIMD[.uint8, width]()
    comptime for lane in range(width):
        var bits = 0
        comptime for option in range(alternation.count):
            comptime byte = Int(
                _alternation_byte[
                    nodes, alternation, position, False, casefold, option
                ]()
            )
            comptime value = (byte >> 4) if high else (byte & 0xF)
            comptime if value == lane % 16:
                bits |= 1 << option
        table[lane] = UInt8(bits)
    return table


@always_inline
def _avx512_nibble_lookup[
    width: Int
](table: SIMD[.uint8, width], values: SIMD[.uint8, width]) -> SIMD[
    .uint8, width
]:
    var indices = values & SIMD[.uint8, width](0xF)
    return llvm_intrinsic[
        "llvm.x86.avx512.pshuf.b.512",
        SIMD[.uint8, width],
        has_side_effect=False,
    ](table, indices)


@always_inline
def _literal_alternation_teddy_mask[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](
    first_values: SIMD[.uint8, width],
    second_values: SIMD[.uint8, width],
    eighth_values: SIMD[.uint8, width],
) -> SIMD[.bool, width]:
    comptime first_literal = nodes[alternation.options[0]][LiteralNode]
    comptime common_first = first_literal.value.as_bytes()[0]
    var pattern_bits = _alternation_teddy_position_bits[
        nodes, alternation, 1, False, width
    ](second_values)
    pattern_bits &= _alternation_teddy_position_bits[
        nodes, alternation, 7, False, width
    ](eighth_values)
    return first_values.eq(SIMD[.uint8, width](common_first)) & pattern_bits.ne(
        SIMD[.uint8, width](0)
    )


@always_inline
def _alternation_teddy_position_bits[
    nodes: List[RegexNode],
    alternation: OrNode,
    position: Int,
    casefold: Bool,
    width: Int,
](values: SIMD[.uint8, width]) -> SIMD[.uint8, width]:
    var indexed = values
    comptime if casefold:
        indexed |= SIMD[.uint8, width](0x20)
    var low = _avx512_nibble_lookup[width](
        _alternation_nibble_table[
            nodes, alternation, position, casefold, False, width
        ](),
        indexed,
    )
    var high = _avx512_nibble_lookup[width](
        _alternation_nibble_table[
            nodes, alternation, position, casefold, True, width
        ](),
        indexed >> SIMD[.uint8, width](4),
    )
    return low & high


@always_inline
def _alternation_teddy3_mask[
    nodes: List[RegexNode], alternation: OrNode, casefold: Bool, width: Int
](
    first_values: SIMD[.uint8, width],
    second_values: SIMD[.uint8, width],
    third_values: SIMD[.uint8, width],
) -> SIMD[.bool, width]:
    """Use three correlated nibble tables for up to eight literals."""
    var pattern_bits = _alternation_teddy_position_bits[
        nodes, alternation, 0, casefold, width
    ](first_values)
    pattern_bits &= _alternation_teddy_position_bits[
        nodes, alternation, 1, casefold, width
    ](second_values)
    pattern_bits &= _alternation_teddy_position_bits[
        nodes, alternation, 2, casefold, width
    ](third_values)
    return pattern_bits.ne(0)


@always_inline
def _literal_alternation_candidate_mask[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](text: ImmStringSpan, offset: Int, first_values: SIMD[.uint8, width]) -> SIMD[
    .bool, width
]:
    comptime first_literal = nodes[alternation.options[0]][LiteralNode]
    comptime first_byte = Int(first_literal.value.as_bytes()[0])
    comptime if (
        width == 64
        and 4 <= alternation.count <= 8
        and (
            first_byte < 0x80
            or not _literal_alternation_same_first_byte[nodes, alternation]()
        )
        and _all_literal_options[nodes, alternation, 3]()
        and CompilationTarget.is_x86()
        and CompilationTarget.has_avx512f()
    ):
        var second_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 1)
        var third_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 2)
        return _alternation_teddy3_mask[nodes, alternation, False, width](
            first_values, second_values, third_values
        )
    elif (
        alternation.count >= 4
        and first_byte >= 0x80
        and _literal_alternation_same_first_byte[nodes, alternation]()
        and _all_literal_options[nodes, alternation, 8]()
    ):
        var second_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 1)
        var eighth_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 7)
        comptime if (
            width == 64
            and alternation.count <= 8
            and CompilationTarget.is_x86()
            and CompilationTarget.has_avx512f()
        ):
            return _literal_alternation_teddy_mask[nodes, alternation, width](
                first_values, second_values, eighth_values
            )
        else:
            comptime first = nodes[alternation.options[0]][
                LiteralNode
            ].value.as_bytes()[0]
            return first_values.eq(first) & _alternation_two_position_mask[
                nodes, alternation, 1, 7, False, width
            ](second_values, eighth_values)
    elif (
        alternation.count >= 4 and _all_literal_options[nodes, alternation, 3]()
    ):
        var second_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 1)
        var third_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 2)
        return _literal_alternation_three_byte_mask[nodes, alternation, width](
            first_values, second_values, third_values
        )
    elif _all_literal_options[nodes, alternation, 3]():
        var third_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 2)
        return _alternation_two_position_mask[
            nodes, alternation, 0, 2, False, width
        ](first_values, third_values)
    elif _all_literal_options[nodes, alternation, 2]():
        var second_values = text.unsafe_ptr().unsafe_load[
            width=width, alignment=1
        ](offset + 1)
        return _alternation_two_position_mask[
            nodes, alternation, 0, 1, False, width
        ](first_values, second_values)
    else:
        return _literal_alternation_full_mask[nodes, alternation, width](
            text, offset, first_values
        )


@always_inline
def _literal_alternation_match_length_at[
    nodes: List[RegexNode], alternation: OrNode
](text: ImmStringSpan, start: Int) -> Int:
    comptime for i in range(alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        comptime literal_length = literal.value.byte_length()
        if start + literal_length > text.byte_length():
            continue
        comptime if literal_length >= 2:
            comptime second = literal.value.as_bytes()[1]
            if text.as_bytes()[start + 1] != second:
                continue
        if _match_literal[literal.value](text, start):
            return literal.value.byte_length()
    return 0


@always_inline
def _count_literal_alternation_find[
    nodes: List[RegexNode], alternation: OrNode, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Merge full-literal search streams when all first bytes collide."""
    var candidates = StaticTuple[Int, MAX_BRANCHES]()
    comptime for i in range(alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        candidates[i] = text.find(literal.value)

    var total = 0
    while True:
        var earliest = -1
        comptime for i in range(alternation.count):
            if candidates[i] >= 0 and (
                earliest < 0 or candidates[i] < earliest
            ):
                earliest = candidates[i]
        if earliest < 0:
            break

        var match_length = 0
        comptime for i in range(alternation.count):
            comptime literal = nodes[alternation.options[i]][LiteralNode]
            if match_length == 0 and candidates[i] == earliest:
                match_length = literal.value.byte_length()
        total += _match_checksum[sum_spans](match_length)
        var next_start = earliest + match_length

        comptime for i in range(alternation.count):
            if candidates[i] >= 0 and candidates[i] < next_start:
                comptime literal = nodes[alternation.options[i]][LiteralNode]
                candidates[i] = text.find(literal.value, next_start)
    return total


@always_inline
def _count_literal_alternation[
    nodes: List[RegexNode], alternation: OrNode, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count literal alternatives using SIMD prefix candidate masks."""
    comptime first_literal = nodes[alternation.options[0]][LiteralNode]
    comptime first_byte = Int(first_literal.value.as_bytes()[0])
    comptime if (
        alternation.count >= 4
        and first_byte < 0x80
        and _literal_alternation_same_first_byte[nodes, alternation]()
    ):
        return _count_literal_alternation_find[nodes, alternation, sum_spans](
            text
        )
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    var pointer = text.unsafe_ptr()
    while offset + CLASS_SIMD_WIDTH <= length:
        if not _literal_alternation_block_fits[
            nodes, alternation, CLASS_SIMD_WIDTH
        ](length, offset):
            break
        var first_values = pointer.unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](offset)
        var candidates = _literal_alternation_candidate_mask[
            nodes, alternation, CLASS_SIMD_WIDTH
        ](text, offset, first_values)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var start = offset + lane
            if start >= next_start:
                var match_length = _literal_alternation_match_length_at[
                    nodes, alternation
                ](text, start)
                if match_length > 0:
                    total += _match_checksum[sum_spans](match_length)
                    next_start = start + match_length
        offset += CLASS_SIMD_WIDTH

    while offset < length:
        if offset >= next_start:
            var match_length = _literal_alternation_match_length_at[
                nodes, alternation
            ](text, offset)
            if match_length > 0:
                total += _match_checksum[sum_spans](match_length)
                next_start = offset + match_length
        offset += 1
    return total


@always_inline
def _search_literal_alternation[
    nodes: List[RegexNode], alternation: OrNode
](text: ImmStringSpan) -> Bool:
    # Search once for the union of all first bytes. Full literal comparisons
    # are only evaluated in vector blocks that contain a candidate.
    var length = text.byte_length()
    var pointer = text.unsafe_ptr()
    var offset = 0
    while offset + CLASS_SIMD_WIDTH <= length:
        var values = pointer.unsafe_load[width=CLASS_SIMD_WIDTH, alignment=1](
            offset
        )
        var candidates = SIMD[.bool, CLASS_SIMD_WIDTH](fill=False)
        comptime for i in range(alternation.count):
            comptime literal = nodes[alternation.options[i]][LiteralNode]
            comptime first = literal.value.as_bytes()[0]
            candidates |= values.eq(SIMD[.uint8, CLASS_SIMD_WIDTH](first))
        if any(candidates):
            if _literal_alternation_block_fits[
                nodes, alternation, CLASS_SIMD_WIDTH
            ](length, offset):
                if _literal_alternation_block_matches[
                    nodes, alternation, CLASS_SIMD_WIDTH
                ](text, offset, values):
                    return True
                offset += CLASS_SIMD_WIDTH
            else:
                var end = offset + CLASS_SIMD_WIDTH
                while offset < end:
                    if _literal_alternation_matches_at[nodes, alternation](
                        text, offset
                    ):
                        return True
                    offset += 1
        else:
            offset += CLASS_SIMD_WIDTH

    while offset < length:
        if _literal_alternation_matches_at[nodes, alternation](text, offset):
            return True
        offset += 1
    return False
