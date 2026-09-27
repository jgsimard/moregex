"""Neutral scanning primitives shared by search and aggregation."""

from ._simd import _consume_simd_width_ladder

from ._ast import RegexNode
from ._analysis import (
    _bounded_repeat_byte_accepts,
    _fixed_node_mask,
    _one_byte_atom_accepts,
)
from ._common import (
    CLASS_TAIL_SIMD_WIDTH,
)


@always_inline
def _contains_one_byte_node[
    nodes: List[RegexNode], node_index: Int
](text: ImmStringSpan) -> Bool:
    """Return whether a byte predicate occurs."""
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
def _search_one_byte_run[
    nodes: List[RegexNode], child: Int, minimum: Int
](text: ImmStringSpan) -> Bool:
    """Search for a consecutive run accepted by one AST node."""
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
