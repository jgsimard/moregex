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
    __match lhs:
    case .Empty:
        return rhs.isa[EmptyNode]()
    case .Literal(ref lhs_literal):
        return rhs.isa[LiteralNode]() and (
            lhs_literal.value == rhs[LiteralNode].value
        )
    case .CharClass(ref lhs_class):
        return rhs.isa[CharClassNode]() and (
            lhs_class.kind == rhs[CharClassNode].kind
        )
    case .BracketClass(ref lhs_bracket):
        return rhs.isa[BracketClassNode]() and _same_bracket_class(
            lhs_bracket, rhs[BracketClassNode]
        )
    case .ZeroWidth(ref lhs_zero_width):
        return rhs.isa[ZeroWidthNode]() and (
            lhs_zero_width.kind == rhs[ZeroWidthNode].kind
        )
    case .Or(ref lhs_or):
        if not rhs.isa[OrNode]():
            return False
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
    case .Repeat(ref lhs_repeat):
        if not rhs.isa[RepeatNode]():
            return False
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
    case .Sequence(ref lhs_sequence):
        if not rhs.isa[SequenceNode]():
            return False
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
    case .Capture(ref lhs_capture):
        if not rhs.isa[CaptureNode]():
            return False
        ref rhs_capture = rhs[CaptureNode]
        return lhs_capture.index == rhs_capture.index and _same_ast_node(
            lhs_nodes,
            lhs_capture.child,
            rhs_nodes,
            rhs_capture.child,
        )
