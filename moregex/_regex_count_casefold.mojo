"""Specialized case-folded count kernels."""

from ._ast import (
    BracketClassNode,
    OrNode,
    RegexNode,
    SequenceNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits
from std.sys import CompilationTarget

from ._regex_common import (
    CLASS_SIMD_WIDTH,
    _bracket_accepts,
    _match_checksum,
)

from ._regex_analysis import (
    _bracket_mask,
    _fixed_node_mask,
    _fixed_node_width,
)

from ._regex_matcher import _match_node


from ._regex_literals import (
    _alternation_teddy3_mask,
)


@always_inline
def _casefold_alternation_prefix_mask[
    nodes: List[RegexNode], alternation: OrNode, width: Int
](text: ImmStringSpan, offset: Int) -> SIMD[.bool, width]:
    var pointer = text.unsafe_ptr()
    var first_values = pointer.unsafe_load[width=width, alignment=1](offset)
    var second_values = pointer.unsafe_load[width=width, alignment=1](
        offset + 1
    )
    var third_values = pointer.unsafe_load[width=width, alignment=1](offset + 2)
    comptime if (
        width == 64
        and alternation.count <= 8
        and CompilationTarget.is_x86()
        and CompilationTarget.has_avx512f()
    ):
        return _alternation_teddy3_mask[nodes, alternation, True, width](
            first_values, second_values, third_values
        )
    var candidates = SIMD[.bool, width](fill=False)
    comptime for i in range(alternation.count):
        comptime sequence = nodes[alternation.options[i]][SequenceNode]
        comptime first = nodes[sequence.items[0]][BracketClassNode]
        comptime second = nodes[sequence.items[1]][BracketClassNode]
        comptime third = nodes[sequence.items[2]][BracketClassNode]
        candidates |= (
            _bracket_mask[first, width](first_values)
            & _bracket_mask[second, width](second_values)
            & _bracket_mask[third, width](third_values)
        )
    return candidates


@always_inline
def _casefold_alternation_match_length_at[
    nodes: List[RegexNode], alternation: OrNode
](text: ImmStringSpan, start: Int) -> Int:
    """Verify a folded-literal candidate without generic alternation dispatch.
    """
    comptime for i in range(alternation.count):
        comptime option_index = alternation.options[i]
        comptime sequence = nodes[option_index][SequenceNode]
        comptime match_width = _fixed_node_width[nodes, option_index]()
        comptime if match_width > 0:
            comptime first = nodes[sequence.items[0]][BracketClassNode]
            comptime second = nodes[sequence.items[1]][BracketClassNode]
            comptime third = nodes[sequence.items[2]][BracketClassNode]
            if start + match_width > text.byte_length():
                continue
            if not (
                _bracket_accepts[first](Int(text.as_bytes()[start]))
                and _bracket_accepts[second](Int(text.as_bytes()[start + 1]))
                and _bracket_accepts[third](Int(text.as_bytes()[start + 2]))
            ):
                continue
            if all(_fixed_node_mask[nodes, option_index, 1, 0](text, start)):
                return match_width
        else:
            var result = _match_node[nodes, option_index](text, start)
            if result:
                return result.unsafe_value().consumed()
    return 0


@always_inline
def _count_casefold_prefixed_alternation[
    regex: Regex, alternation: OrNode, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """SIMD-prefilter alternatives by their first three folded letters."""
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    while offset + CLASS_SIMD_WIDTH + 2 <= length:
        var candidates = _casefold_alternation_prefix_mask[
            regex.nodes, alternation, CLASS_SIMD_WIDTH
        ](text, offset)
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var start = offset + lane
            if start >= next_start:
                var match_length = _casefold_alternation_match_length_at[
                    regex.nodes, alternation
                ](text, start)
                if match_length > 0:
                    total += _match_checksum[sum_spans](match_length)
                    next_start = start + match_length
        offset += CLASS_SIMD_WIDTH

    while offset + 2 < length:
        if offset >= next_start:
            var match_length = _casefold_alternation_match_length_at[
                regex.nodes, alternation
            ](text, offset)
            if match_length > 0:
                total += _match_checksum[sum_spans](match_length)
                next_start = offset + match_length
        offset += 1
    return total
