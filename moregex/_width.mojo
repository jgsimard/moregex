"""Shared regex AST width analysis.

This module owns the byte-width definitions used by semantic validation and
execution planning so those layers cannot silently diverge.
"""

from ._ast import (
    ASSERT_INPUT_END,
    ASSERT_INPUT_START,
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
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


def _semantic_minimum_width(nodes: List[RegexNode], node_index: Int) -> Int:
    """Return the minimum bytes consumed by any successful match."""
    ref node = nodes[node_index]
    if node.isa[EmptyNode]() or node.isa[ZeroWidthNode]():
        return 0
    if node.isa[LiteralNode]():
        return node[LiteralNode].value.byte_length()
    if node.isa[CharClassNode]() or node.isa[BracketClassNode]():
        return 1
    if node.isa[CaptureNode]():
        return _semantic_minimum_width(nodes, node[CaptureNode].child)
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        if alternation.count == 0:
            return 0
        var width = _semantic_minimum_width(nodes, alternation.options[0])
        for i in range(1, alternation.count):
            width = min(
                width,
                _semantic_minimum_width(nodes, alternation.options[i]),
            )
        return width
    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        return repeat.minimum * _semantic_minimum_width(nodes, repeat.child)

    ref sequence = node[SequenceNode]
    var width = 0
    for i in range(sequence.count):
        width += _semantic_minimum_width(nodes, sequence.items[i])
    return width


def _semantic_fixed_width(
    nodes: List[RegexNode],
    node_index: Int,
    assertions_are_zero_width: Bool = True,
) -> Int:
    """Return an exact byte width, or -1 when it is variable.

    Optimizer prefilters pass `False` because width alone cannot preserve an
    assertion. Semantic validation uses the exact zero-byte assertion width.
    """
    ref node = nodes[node_index]
    if node.isa[EmptyNode]():
        return 0
    if node.isa[ZeroWidthNode]():
        return 0 if assertions_are_zero_width else -1
    if node.isa[LiteralNode]():
        return node[LiteralNode].value.byte_length()
    if node.isa[CharClassNode]():
        var kind = node[CharClassNode].kind
        return -1 if (
            kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL
        ) else 1
    if node.isa[BracketClassNode]():
        return 1
    if node.isa[CaptureNode]():
        return _semantic_fixed_width(
            nodes, node[CaptureNode].child, assertions_are_zero_width
        )
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        if alternation.count == 0:
            return 0
        var width = _semantic_fixed_width(
            nodes, alternation.options[0], assertions_are_zero_width
        )
        if width < 0:
            return -1
        for i in range(1, alternation.count):
            if (
                _semantic_fixed_width(
                    nodes,
                    alternation.options[i],
                    assertions_are_zero_width,
                )
                != width
            ):
                return -1
        return width
    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        if repeat.maximum != repeat.minimum:
            return -1
        var child_width = _semantic_fixed_width(
            nodes, repeat.child, assertions_are_zero_width
        )
        return -1 if child_width < 0 else repeat.minimum * child_width

    ref sequence = node[SequenceNode]
    var width = 0
    for i in range(sequence.count):
        var child_width = _semantic_fixed_width(
            nodes, sequence.items[i], assertions_are_zero_width
        )
        if child_width < 0:
            return -1
        width += child_width
    return width


def _semantic_maximum_width(nodes: List[RegexNode], node_index: Int) -> Int:
    """Return the maximum consumed byte width, or -1 when unbounded."""
    ref node = nodes[node_index]
    if node.isa[EmptyNode]() or node.isa[ZeroWidthNode]():
        return 0
    if node.isa[LiteralNode]():
        return node[LiteralNode].value.byte_length()
    if node.isa[CharClassNode]():
        var kind = node[CharClassNode].kind
        return 4 if (
            kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL
        ) else 1
    if node.isa[BracketClassNode]():
        return 1
    if node.isa[CaptureNode]():
        return _semantic_maximum_width(nodes, node[CaptureNode].child)
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        var width = 0
        for i in range(alternation.count):
            var option_width = _semantic_maximum_width(
                nodes, alternation.options[i]
            )
            if option_width < 0:
                return -1
            width = max(width, option_width)
        return width
    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        if repeat.maximum == 0:
            return 0
        if repeat.maximum < 0:
            return -1
        var child_width = _semantic_maximum_width(nodes, repeat.child)
        return -1 if child_width < 0 else repeat.maximum * child_width

    ref sequence = node[SequenceNode]
    var width = 0
    for i in range(sequence.count):
        var child_width = _semantic_maximum_width(nodes, sequence.items[i])
        if child_width < 0:
            return -1
        width += child_width
    return width


def _minimum_node_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return the minimum bytes consumed by any successful match."""
    return comptime (_semantic_minimum_width(nodes, node_index))


def _maximum_node_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return the maximum bytes consumed, or -1 when unbounded."""
    return comptime (_semantic_maximum_width(nodes, node_index))


def _fixed_node_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return a node's exact byte width, or -1 when it is variable."""
    return comptime (_semantic_fixed_width(nodes, node_index, False))


def _is_start_assertion_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[ZeroWidthNode]():
        return node[ZeroWidthNode].kind == ASSERT_INPUT_START
    return False


def _is_end_assertion_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[ZeroWidthNode]():
        return node[ZeroWidthNode].kind == ASSERT_INPUT_END
    return False


def _semantic_is_start_anchored(
    nodes: List[RegexNode], node_index: Int
) -> Bool:
    """Return whether the expression can only match at byte zero."""
    ref node = nodes[node_index]
    if node.isa[ZeroWidthNode]():
        return node[ZeroWidthNode].kind == ASSERT_INPUT_START
    if node.isa[SequenceNode]():
        ref sequence = node[SequenceNode]
        for i in range(sequence.count):
            ref item = nodes[sequence.items[i]]
            if item.isa[EmptyNode]():
                continue
            if item.isa[ZeroWidthNode]():
                if item[ZeroWidthNode].kind == ASSERT_INPUT_START:
                    return True
                continue
            return False
    return False


def _is_start_anchored[nodes: List[RegexNode], node_index: Int]() -> Bool:
    return comptime (_semantic_is_start_anchored(nodes, node_index))


def _is_end_anchored[nodes: List[RegexNode], node_index: Int]() -> Bool:
    """Return whether the expression requires input end (or its final LF)."""
    comptime node = nodes[node_index]
    comptime if _is_end_assertion_node[nodes, node_index]():
        return True
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime for offset in range(sequence.count):
            comptime i = sequence.count - offset - 1
            comptime item = nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]():
                continue
            comptime if item.isa[ZeroWidthNode]():
                comptime if _is_end_assertion_node[nodes, sequence.items[i]]():
                    return True
                continue
            return False
    return False


def _fixed_sequence_prefix_width[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    comptime if item == sequence.count - 1:
        return 0
    else:
        comptime width = _fixed_node_width[nodes, sequence.items[item]]()
        comptime suffix_width = _fixed_sequence_prefix_width[
            nodes, sequence, item + 1
        ]()
        comptime if width < 0 or suffix_width < 0:
            return -1
        return width + suffix_width


def _end_anchored_fixed_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return consuming width for fixed-width followed by input end."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count >= 2:
            comptime if _is_end_assertion_node[
                nodes, sequence.items[sequence.count - 1]
            ]():
                return _fixed_sequence_prefix_width[nodes, sequence, 0]()
    return -1
