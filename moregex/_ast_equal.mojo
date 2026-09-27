"""Structural equality helpers for normalized regex ASTs."""

from ._ast import (
    BracketClassNode,
    CaptureNode,
    CharClassNode,
    EmptyNode,
    LiteralNode,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)


def _same_bracket_ranges(
    left: BracketClassNode, right: BracketClassNode
) -> Bool:
    """Compare the canonical ranges, independently of negation."""
    if left.count != right.count:
        return False
    for i in range(left.count):
        if left.lows[i] != right.lows[i] or left.highs[i] != right.highs[i]:
            return False
    return True


def _same_bracket_class(
    left: BracketClassNode, right: BracketClassNode
) -> Bool:
    return left.negated == right.negated and _same_bracket_ranges(left, right)


def _same_ast_node(
    lhs_nodes: List[RegexNode],
    lhs_index: Int,
    rhs_nodes: List[RegexNode],
    rhs_index: Int,
) -> Bool:
    """Recursively compare two normalized AST subtrees."""
    ref lhs = lhs_nodes[lhs_index]
    ref rhs = rhs_nodes[rhs_index]
    if lhs.isa[EmptyNode]():
        return rhs.isa[EmptyNode]()
    if lhs.isa[LiteralNode]():
        return rhs.isa[LiteralNode]() and (
            lhs[LiteralNode].value == rhs[LiteralNode].value
        )
    if lhs.isa[CharClassNode]():
        return rhs.isa[CharClassNode]() and (
            lhs[CharClassNode].kind == rhs[CharClassNode].kind
        )
    if lhs.isa[BracketClassNode]():
        return rhs.isa[BracketClassNode]() and _same_bracket_class(
            lhs[BracketClassNode], rhs[BracketClassNode]
        )
    if lhs.isa[ZeroWidthNode]():
        return rhs.isa[ZeroWidthNode]() and (
            lhs[ZeroWidthNode].kind == rhs[ZeroWidthNode].kind
        )
    if lhs.isa[OrNode]():
        if not rhs.isa[OrNode]():
            return False
        ref lhs_or = lhs[OrNode]
        ref rhs_or = rhs[OrNode]
        if lhs_or.count != rhs_or.count:
            return False
        for i in range(lhs_or.count):
            if not _same_ast_node(
                lhs_nodes,
                lhs_or.options[i],
                rhs_nodes,
                rhs_or.options[i],
            ):
                return False
        return True
    if lhs.isa[RepeatNode]():
        if not rhs.isa[RepeatNode]():
            return False
        ref lhs_repeat = lhs[RepeatNode]
        ref rhs_repeat = rhs[RepeatNode]
        return (
            lhs_repeat.minimum == rhs_repeat.minimum
            and lhs_repeat.maximum == rhs_repeat.maximum
            and lhs_repeat.greedy == rhs_repeat.greedy
            and _same_ast_node(
                lhs_nodes,
                lhs_repeat.child,
                rhs_nodes,
                rhs_repeat.child,
            )
        )
    if lhs.isa[SequenceNode]():
        if not rhs.isa[SequenceNode]():
            return False
        ref lhs_sequence = lhs[SequenceNode]
        ref rhs_sequence = rhs[SequenceNode]
        if lhs_sequence.count != rhs_sequence.count:
            return False
        for i in range(lhs_sequence.count):
            if not _same_ast_node(
                lhs_nodes,
                lhs_sequence.items[i],
                rhs_nodes,
                rhs_sequence.items[i],
            ):
                return False
        return True
    if not lhs.isa[CaptureNode]() or not rhs.isa[CaptureNode]():
        return False
    ref lhs_capture = lhs[CaptureNode]
    ref rhs_capture = rhs[CaptureNode]
    return lhs_capture.index == rhs_capture.index and _same_ast_node(
        lhs_nodes,
        lhs_capture.child,
        rhs_nodes,
        rhs_capture.child,
    )
