"""Compile-time checks for regex execution-semantic coverage."""

from ._ast import (
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
    BracketClassNode,
    CharClassNode,
    EmptyNode,
    LiteralNode,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)


comptime MAX_NFA_REPEAT_EXPANSION = 256


def _semantic_fixed_width(
    nodes: List[RegexNode],
    node_index: Int,
    assertions_are_zero_width: Bool = True,
) -> Int:
    """Return a byte width, or -1 when the node is variable-width.

    Optimizer prefilters pass `False` because they cannot preserve assertion
    semantics from width alone; NFA eligibility uses the exact zero-byte width.
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
                    nodes, alternation.options[i], assertions_are_zero_width
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


def _nfa_match_semantics_required(
    nodes: List[RegexNode],
    node_index: Int,
    has_suffix: Bool,
    require_end: Bool,
) -> Bool:
    """Whether this AST context needs ordered NFA path exploration."""
    ref node = nodes[node_index]
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        if (has_suffix or require_end) and _semantic_fixed_width(
            nodes, node_index
        ) < 0:
            return True
        for i in range(alternation.count):
            if _nfa_match_semantics_required(
                nodes,
                alternation.options[i],
                has_suffix,
                require_end,
            ):
                return True
        return False
    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        if (has_suffix or require_end) and not repeat.greedy:
            return True
        ref child = nodes[repeat.child]
        if has_suffix and _semantic_fixed_width(nodes, repeat.child) < 0:
            return True
        if (
            require_end
            and _semantic_fixed_width(nodes, repeat.child) < 0
            and not child.isa[CharClassNode]()
        ):
            return True
        return _nfa_match_semantics_required(nodes, repeat.child, True, False)
    if node.isa[SequenceNode]():
        ref sequence = node[SequenceNode]
        for i in range(sequence.count):
            var child_index = sequence.items[i]
            if _nfa_match_semantics_required(
                nodes,
                child_index,
                has_suffix or i + 1 < sequence.count,
                require_end and i + 1 == sequence.count,
            ):
                return True
    return False


def _nfa_full_semantics_required(nodes: List[RegexNode], root: Int) -> Bool:
    return _nfa_match_semantics_required(nodes, root, False, True)


def _nfa_partial_semantics_required(nodes: List[RegexNode], root: Int) -> Bool:
    return _nfa_match_semantics_required(nodes, root, False, False)


def _nfa_node_supported(nodes: List[RegexNode], node_index: Int) -> Bool:
    """Whether Thompson compilation stays within its expansion limit."""
    ref node = nodes[node_index]
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        for i in range(alternation.count):
            if not _nfa_node_supported(nodes, alternation.options[i]):
                return False
    elif node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        if repeat.minimum > MAX_NFA_REPEAT_EXPANSION or (
            repeat.maximum >= 0 and repeat.maximum > MAX_NFA_REPEAT_EXPANSION
        ):
            return False
        return _nfa_node_supported(nodes, repeat.child)
    elif node.isa[SequenceNode]():
        ref sequence = node[SequenceNode]
        for i in range(sequence.count):
            if not _nfa_node_supported(nodes, sequence.items[i]):
                return False
    return True


def _semantics_supported(nodes: List[RegexNode], root: Int) -> Bool:
    return not _nfa_full_semantics_required(nodes, root) or _nfa_node_supported(
        nodes, root
    )
