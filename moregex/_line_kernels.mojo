"""Line-oriented aggregation kernels."""

from ._ast import (
    LiteralNode,
    RepeatNode,
    SequenceNode,
)
from ._syntax import Regex

from ._common import (
    _match_literal,
)

from ._analysis import (
    _AnchoredLazyLiteralPlan,
    _LinePrefixRunLiteralPlan,
    _anchored_prefix_delimited_line_offset,
    _node_start_accepts,
)


from ._ast_matcher import (
    _match_sequence_from,
    _match_node,
)


@always_inline
def _count_anchored_prefix_delimited_lines[
    regex: Regex
](text: ImmStringSpan) -> Int:
    """Count grep lines matching an AST-normalized prefix/delimiter shape."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime item_offset = _anchored_prefix_delimited_line_offset[
        regex.nodes, regex.root
    ]()
    comptime prefix = regex.nodes[sequence.items[1 + item_offset]][RepeatNode]
    var bytes = text.as_bytes()
    var length = text.byte_length()
    var total = 0
    var line_start = 0
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = length if newline < 0 else newline
        if line_end > line_start and Int(bytes[line_end - 1]) == ord("\r"):
            line_end -= 1
        var position = line_start
        while position < line_end and _node_start_accepts[
            regex.nodes, prefix.child
        ](Int(bytes[position])):
            position += 1
        if position < line_end and _node_start_accepts[
            regex.nodes, sequence.items[2 + item_offset]
        ](Int(bytes[position])):
            position += 1
            if position < line_end and _node_start_accepts[
                regex.nodes, sequence.items[4 + item_offset]
            ](Int(bytes[line_end - 1])):
                total += 1
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def _count_anchored_lazy_literal_lines[
    regex: Regex, plan: _AnchoredLazyLiteralPlan
](text: ImmStringSpan) -> Int:
    """Count anchored lines using the literal after a lazy dot as the anchor."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime prefix_literal = regex.nodes[plan.prefix_literal_index][
        LiteralNode
    ]
    comptime search_literal = regex.nodes[plan.search_literal_index][
        LiteralNode
    ]
    var total = 0
    var line_start = 0
    var length = text.byte_length()
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = newline
        if newline < 0:
            line_end = length
        if line_end > line_start and Int(text.as_bytes()[line_end - 1]) == 13:
            line_end -= 1
        var line = text[byte=line_start:line_end]
        var prefix = _match_node[regex.nodes, plan.prefix_repeat_index](line, 0)
        var prefix_end = prefix.unsafe_value().consumed()
        if _match_literal[prefix_literal.value](line, prefix_end):
            var candidate = line.find(
                search_literal.value,
                prefix_end + prefix_literal.value.byte_length(),
            )
            while candidate >= 0:
                var suffix = _match_sequence_from[
                    regex.nodes, sequence, plan.suffix_item
                ](
                    line,
                    candidate + search_literal.value.byte_length(),
                )
                if suffix:
                    total += 1
                    break
                candidate = line.find(search_literal.value, candidate + 1)
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def _count_line_prefix_run_literal[
    regex: Regex, plan: _LinePrefixRunLiteralPlan
](text: ImmStringSpan) -> Int:
    """Count lines matching a deterministic anchored run/literal prefix."""
    comptime literal = regex.nodes[plan.literal_index][LiteralNode]
    var total = 0
    var line_start = 0
    var length = text.byte_length()
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = newline
        if newline < 0:
            line_end = length
        if line_end > line_start and Int(text.as_bytes()[line_end - 1]) == 13:
            line_end -= 1
        var line = text[byte=line_start:line_end]
        var prefix = _match_node[regex.nodes, plan.repeat_index](line, 0)
        var position = prefix.unsafe_value().consumed()
        if (
            position + literal.value.byte_length() <= line.byte_length()
            and _match_literal[literal.value](line, position)
        ):
            total += 1
        if newline < 0:
            break
        line_start = newline + 1
    return total
