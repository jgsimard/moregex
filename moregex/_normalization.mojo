"""Post-parse AST normalization and capture-erased views."""

from std.utils import StaticTuple


from ._ast import (
    BracketClassNode,
    CaptureNode,
    LiteralNode,
    MAX_BRANCHES,
    MAX_CLASS_RANGES,
    MAX_SEQUENCE_ITEMS,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
)

from ._ast_equal import _same_bracket_class


@always_inline
def _append_range(
    mut lows: List[Int], mut highs: List[Int], low: Int, high: Int
):
    var sorted_lows = lows.copy()
    var sorted_highs = highs.copy()
    sorted_lows.append(low)
    sorted_highs.append(high)

    for i in range(len(sorted_lows)):
        var best = i
        for j in range(i + 1, len(sorted_lows)):
            if sorted_lows[j] < sorted_lows[best]:
                best = j
        if best != i:
            var saved_low = sorted_lows[i]
            var saved_high = sorted_highs[i]
            sorted_lows[i] = sorted_lows[best]
            sorted_highs[i] = sorted_highs[best]
            sorted_lows[best] = saved_low
            sorted_highs[best] = saved_high

    var merged_lows = List[Int]()
    var merged_highs = List[Int]()
    for i in range(len(sorted_lows)):
        if (
            len(merged_lows) > 0
            and sorted_lows[i] <= merged_highs[len(merged_highs) - 1] + 1
        ):
            merged_highs[len(merged_highs) - 1] = max(
                merged_highs[len(merged_highs) - 1], sorted_highs[i]
            )
        else:
            merged_lows.append(sorted_lows[i])
            merged_highs.append(sorted_highs[i])
    lows = merged_lows^
    highs = merged_highs^


def _add_node(mut nodes: List[RegexNode], var node: RegexNode) -> Int:
    nodes.append(node^)
    return len(nodes) - 1


def _byte_sequence_cardinality(nodes: List[RegexNode], node_index: Int) -> Int:
    """Return the number of byte strings represented by a bracket sequence."""
    ref sequence = nodes[node_index][SequenceNode]
    var cardinality = 1
    for i in range(sequence.count):
        ref bracket = nodes[sequence.items[i]][BracketClassNode]
        var choices = 0
        for item in range(bracket.count):
            choices += bracket.highs[item] - bracket.lows[item] + 1
        cardinality *= choices
    return cardinality


def _append_without_captures(
    nodes: List[RegexNode], node_index: Int, mut result: List[RegexNode]
) -> Int:
    """Rebuild only capture-bearing AST paths while sharing unchanged nodes."""
    ref node = nodes[node_index]
    if node.isa[CaptureNode]():
        return _append_without_captures(nodes, node[CaptureNode].child, result)

    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        var child = _append_without_captures(nodes, repeat.child, result)
        if child == repeat.child:
            return node_index
        result.append(
            RepeatNode(child, repeat.minimum, repeat.maximum, repeat.greedy)
        )
    elif node.isa[SequenceNode]():
        ref sequence = node[SequenceNode]
        var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
        var changed = False
        for i in range(sequence.count):
            items[i] = _append_without_captures(
                nodes, sequence.items[i], result
            )
            changed = changed or items[i] != sequence.items[i]
        if not changed:
            return node_index
        result.append(SequenceNode(items, sequence.count))
    elif node.isa[OrNode]():
        ref alternation = node[OrNode]
        var options = StaticTuple[Int, MAX_BRANCHES]()
        var changed = False
        for i in range(alternation.count):
            options[i] = _append_without_captures(
                nodes, alternation.options[i], result
            )
            changed = changed or options[i] != alternation.options[i]
        if not changed:
            return node_index
        result.append(OrNode(options, alternation.count))
    else:
        return node_index
    return len(result) - 1


def _normalize_literal_cartesian(
    mut nodes: List[RegexNode], root_index: Int
) -> Int:
    """Factor a complete ASCII literal product into a bracket sequence."""
    ref root_node = nodes[root_index]
    if not root_node.isa[OrNode]():
        return root_index
    var alternation = root_node[OrNode]
    if alternation.count < 2:
        return root_index
    ref first_node = nodes[alternation.options[0]]
    if not first_node.isa[LiteralNode]():
        return root_index
    var byte_length = first_node[LiteralNode].value.byte_length()
    if byte_length == 0 or byte_length > MAX_SEQUENCE_ITEMS:
        return root_index
    for option in range(alternation.count):
        ref node = nodes[alternation.options[option]]
        if (
            not node.isa[LiteralNode]()
            or node[LiteralNode].value.byte_length() != byte_length
        ):
            return root_index
        for position in range(byte_length):
            if Int(node[LiteralNode].value.as_bytes()[position]) >= 128:
                return root_index
        for prior in range(option):
            ref prior_node = nodes[alternation.options[prior]][LiteralNode]
            if node[LiteralNode].value == prior_node.value:
                return root_index

    var product = 1
    for position in range(byte_length):
        var values = List[Int]()
        for option in range(alternation.count):
            ref literal = nodes[alternation.options[option]][LiteralNode]
            var value = Int(literal.value.as_bytes()[position])
            var present = False
            for existing in values:
                present = present or existing == value
            if not present:
                values.append(value)
        product *= len(values)
        if product > alternation.count:
            return root_index
    if product != alternation.count:
        return root_index

    var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
    for position in range(byte_length):
        var lows = List[Int]()
        var highs = List[Int]()
        for option in range(alternation.count):
            ref literal = nodes[alternation.options[option]][LiteralNode]
            var value = Int(literal.value.as_bytes()[position])
            _append_range(lows, highs, value, value)
        if len(lows) > MAX_CLASS_RANGES:
            return root_index
        var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
        var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
        for item in range(len(lows)):
            static_lows[item] = lows[item]
            static_highs[item] = highs[item]
        items[position] = _add_node(
            nodes, BracketClassNode(static_lows, static_highs, len(lows), False)
        )
    if byte_length == 1:
        return items[0]
    return _add_node(nodes, SequenceNode(items, byte_length))


def _normalize_utf8_class_or(
    mut nodes: List[RegexNode], child_index: Int
) -> Int:
    """Merge sibling one-byte brackets in one UTF-8 class alternation."""
    ref child_node = nodes[child_index]
    if not child_node.isa[OrNode]():
        return child_index
    var alternation = child_node[OrNode]
    var bracket_count = 0
    var has_sequence = False
    var lows = List[Int]()
    var highs = List[Int]()
    for i in range(alternation.count):
        ref option = nodes[alternation.options[i]]
        if option.isa[BracketClassNode]():
            ref bracket = option[BracketClassNode]
            if bracket.negated:
                return child_index
            bracket_count += 1
            for item in range(bracket.count):
                _append_range(
                    lows,
                    highs,
                    bracket.lows[item],
                    bracket.highs[item],
                )
        elif option.isa[SequenceNode]():
            has_sequence = True
        else:
            return child_index
    if bracket_count < 2 or not has_sequence or len(lows) > MAX_CLASS_RANGES:
        return child_index

    var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
    var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
    for i in range(len(lows)):
        static_lows[i] = lows[i]
        static_highs[i] = highs[i]
    var merged = _add_node(
        nodes, BracketClassNode(static_lows, static_highs, len(lows), False)
    )
    var options = StaticTuple[Int, MAX_BRANCHES]()
    var count = 0
    var emitted_bracket = False
    for i in range(alternation.count):
        var option_index = alternation.options[i]
        if nodes[option_index].isa[BracketClassNode]():
            if not emitted_bracket:
                options[count] = merged
                count += 1
                emitted_bracket = True
        else:
            options[count] = option_index
            count += 1
    return _add_node(nodes, OrNode(options, count))


def _normalize_utf8_repeat(
    mut nodes: List[RegexNode], repeat_index: Int
) -> Int:
    ref node = nodes[repeat_index]
    if not node.isa[RepeatNode]():
        return repeat_index
    var repeat = node[RepeatNode]
    var child = _normalize_utf8_class_or(nodes, repeat.child)
    if child == repeat.child:
        return repeat_index
    return _add_node(
        nodes,
        RepeatNode(
            child,
            repeat.minimum,
            repeat.maximum,
            repeat.greedy,
        ),
    )


def _normalize_utf8_repeat_classes(
    mut nodes: List[RegexNode], root_index: Int
) -> Int:
    """Normalize UTF-8 class repeats at the top execution level."""
    ref root = nodes[root_index]
    if root.isa[RepeatNode]():
        return _normalize_utf8_repeat(nodes, root_index)
    if not root.isa[SequenceNode]():
        return root_index
    var sequence = root[SequenceNode]
    var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
    var changed = False
    for i in range(sequence.count):
        items[i] = _normalize_utf8_repeat(nodes, sequence.items[i])
        changed = changed or items[i] != sequence.items[i]
    if not changed:
        return root_index
    return _add_node(nodes, SequenceNode(items, sequence.count))


def _normalize_root_utf8_repeat(
    mut nodes: List[RegexNode], root_index: Int
) -> Int:
    """Factor equal lead-byte classes in a root UTF-8 class repeat."""
    ref root_node = nodes[root_index]
    if not root_node.isa[RepeatNode]():
        return root_index
    var repeat = root_node[RepeatNode]
    ref child_node = nodes[repeat.child]
    if not child_node.isa[OrNode]():
        return root_index
    var alternation = child_node[OrNode]
    for i in range(alternation.count):
        ref option = nodes[alternation.options[i]]
        if option.isa[BracketClassNode]():
            continue
        if not option.isa[SequenceNode]():
            return root_index
        ref sequence = option[SequenceNode]
        if sequence.count != 2:
            return root_index
        if (
            not nodes[sequence.items[0]].isa[BracketClassNode]()
            or not nodes[sequence.items[1]].isa[BracketClassNode]()
        ):
            return root_index

    var used = List[Bool]()
    for _ in range(alternation.count):
        used.append(False)
    var factored = List[Int]()
    var changed = False
    for i in range(alternation.count):
        if used[i]:
            continue
        var option_index = alternation.options[i]
        ref option = nodes[option_index]
        if option.isa[BracketClassNode]():
            factored.append(option_index)
            continue
        ref sequence = option[SequenceNode]
        var first_index = sequence.items[0]
        ref first = nodes[first_index][BracketClassNode]
        ref second = nodes[sequence.items[1]][BracketClassNode]
        if first.negated or second.negated:
            factored.append(option_index)
            continue
        var members = List[Int]()
        members.append(i)
        var lows = List[Int]()
        var highs = List[Int]()
        for item in range(second.count):
            _append_range(lows, highs, second.lows[item], second.highs[item])
        for j in range(i + 1, alternation.count):
            if used[j]:
                continue
            ref candidate_node = nodes[alternation.options[j]]
            if not candidate_node.isa[SequenceNode]():
                continue
            ref candidate = candidate_node[SequenceNode]
            ref candidate_first = nodes[candidate.items[0]][BracketClassNode]
            ref candidate_second = nodes[candidate.items[1]][BracketClassNode]
            if candidate_second.negated or not _same_bracket_class(
                first, candidate_first
            ):
                continue
            members.append(j)
            for item in range(candidate_second.count):
                _append_range(
                    lows,
                    highs,
                    candidate_second.lows[item],
                    candidate_second.highs[item],
                )
        if len(members) == 1 or len(lows) > MAX_CLASS_RANGES:
            factored.append(option_index)
            continue
        changed = True
        for member in members:
            used[member] = True
        var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
        var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
        for item in range(len(lows)):
            static_lows[item] = lows[item]
            static_highs[item] = highs[item]
        var suffix_index = _add_node(
            nodes, BracketClassNode(static_lows, static_highs, len(lows), False)
        )
        var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
        items[0] = first_index
        items[1] = suffix_index
        factored.append(_add_node(nodes, SequenceNode(items, 2)))
    # Equal-width byte-sequence alternatives have identical observable
    # matching behavior. Test broader ranges first so common Unicode
    # blocks do not pay for narrow exceptional branches on every scalar.
    for i in range(len(factored)):
        if not nodes[factored[i]].isa[SequenceNode]():
            continue
        var best = i
        var best_cardinality = _byte_sequence_cardinality(nodes, factored[i])
        for j in range(i + 1, len(factored)):
            if not nodes[factored[j]].isa[SequenceNode]():
                continue
            var cardinality = _byte_sequence_cardinality(nodes, factored[j])
            if cardinality > best_cardinality:
                best = j
                best_cardinality = cardinality
        if best != i:
            var current = factored[i]
            factored[i] = factored[best]
            factored[best] = current
            changed = True
    if not changed:
        return root_index
    var options = StaticTuple[Int, MAX_BRANCHES]()
    for i in range(len(factored)):
        options[i] = factored[i]
    var child_index = _add_node(nodes, OrNode(options, len(factored)))
    return _add_node(
        nodes,
        RepeatNode(
            child_index,
            repeat.minimum,
            repeat.maximum,
            repeat.greedy,
        ),
    )


def _normalize_regex_ast(
    mut nodes: List[RegexNode], root: Int, unicode: Bool
) -> Int:
    var normalized = _normalize_literal_cartesian(nodes, root)
    if unicode:
        normalized = _normalize_utf8_repeat_classes(nodes, normalized)
        normalized = _normalize_root_utf8_repeat(nodes, normalized)
    return normalized
