"""Compile-time checks for regex execution-semantic coverage."""

from ._ast import CharClassNode, OrNode, RegexNode, RepeatNode, SequenceNode
from ._regex_tuning import MAX_NFA_REPEAT_EXPANSION
from ._regex_width import _semantic_fixed_width


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
            ref child = nodes[child_index]
            if child.isa[OrNode]():
                ref alternation = child[OrNode]
                var fixed_options = True
                for option in range(alternation.count):
                    if (
                        _semantic_fixed_width(
                            nodes, alternation.options[option]
                        )
                        < 0
                    ):
                        fixed_options = False
                        break
                if fixed_options:
                    for option in range(alternation.count):
                        if _nfa_match_semantics_required(
                            nodes,
                            alternation.options[option],
                            has_suffix or i + 1 < sequence.count,
                            require_end and i + 1 == sequence.count,
                        ):
                            return True
                    continue
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
