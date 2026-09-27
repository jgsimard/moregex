"""Shared byte masks, character predicates, and NFA assertions."""

from std.utils import StaticTuple

from ._ast import BracketClassNode


@always_inline
def _runtime_bracket_accepts(node: BracketClassNode, value: Int) -> Bool:
    for item in range(node.count):
        if node.lows[item] <= value <= node.highs[item]:
            return not node.negated
    return node.negated


@always_inline
def _build_bracket_masks(node: BracketClassNode) -> StaticTuple[UInt64, 4]:
    """Compile a bracket class into a 256-bit byte lookup table."""
    var masks = StaticTuple[UInt64, 4]()
    for value in range(256):
        if _runtime_bracket_accepts(node, value):
            masks[value // 64] |= UInt64(1) << UInt64(value % 64)
    return masks
