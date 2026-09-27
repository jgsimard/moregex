"""Reference runtime AST interpreter used by tests and benchmarks."""

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
from ._syntax import Regex

from ._regex_masks import _runtime_bracket_accepts
from ._regex_common import (
    _MatchResult,
    _runtime_class_accepts,
    _utf8_codepoint_width,
    _zero_width_matches,
)


def _match_node_runtime(
    nodes: List[RegexNode], node_index: Int, text: String, start: Int
) -> Optional[_MatchResult]:
    ref node = nodes[node_index]
    if node.isa[EmptyNode]():
        return _MatchResult(0)
    if node.isa[LiteralNode]():
        ref value = node[LiteralNode].value
        if start + value.byte_length() > text.byte_length():
            return None
        var text_bytes = text.as_bytes()
        var pattern_bytes = value.as_bytes()
        for i in range(value.byte_length()):
            if text_bytes[start + i] != pattern_bytes[i]:
                return None
        return _MatchResult(value.byte_length())
    if node.isa[CharClassNode]():
        var kind = node[CharClassNode].kind
        if start >= text.byte_length():
            return None
        var value = Int(text.as_bytes()[start])
        if kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL:
            var span = text[byte = 0 : text.byte_length()]
            var width = _utf8_codepoint_width(span, start)
            if width == 0 or (kind == CHAR_UNICODE_DOT and value == ord("\n")):
                return None
            return _MatchResult(width)
        if _runtime_class_accepts(kind, value):
            return _MatchResult(1)
        return None
    if node.isa[BracketClassNode]():
        ref bracket = node[BracketClassNode]
        if start >= text.byte_length():
            return None
        var value = Int(text.as_bytes()[start])
        if _runtime_bracket_accepts(bracket, value):
            return _MatchResult(1)
        return None
    if node.isa[ZeroWidthNode]():
        var kind = node[ZeroWidthNode].kind
        var span = text[byte = 0 : text.byte_length()]
        return _MatchResult(0) if _zero_width_matches(
            kind, span, start
        ) else None
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        for i in range(alternation.count):
            var result = _match_node_runtime(
                nodes, alternation.options[i], text, start
            )
            if result:
                return result^
        return None
    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        var count = 0
        var consumed = 0
        while repeat.maximum < 0 or count < repeat.maximum:
            var result = _match_node_runtime(
                nodes, repeat.child, text, start + consumed
            )
            if not result or result.unsafe_value().consumed() == 0:
                break
            count += 1
            consumed += result.unsafe_value().consumed()
        if count >= repeat.minimum:
            return _MatchResult(consumed)
        return None

    ref sequence = node[SequenceNode]
    var consumed = 0
    for i in range(sequence.count):
        var result = _match_node_runtime(
            nodes, sequence.items[i], text, start + consumed
        )
        if not result:
            return None
        consumed += result.unsafe_value().consumed()
    return _MatchResult(consumed)


@no_inline
def matches_runtime(regex: Regex, text: String) -> Bool:
    """Reference AST interpreter used to quantify specialization overhead."""
    var result = _match_node_runtime(regex.nodes, regex.root, text, 0)
    return result and result.unsafe_value().consumed() == text.byte_length()
