"""Reference runtime AST interpreter used by tests."""

from ._ast import CHAR_UNICODE_DOT, CHAR_UNICODE_DOTALL, RegexNode
from ._syntax import Regex

from ._byte_predicates import _runtime_bracket_accepts
from ._common import (
    _MatchResult,
    _runtime_class_accepts,
    _utf8_codepoint_width,
    _zero_width_matches,
)


def _match_node_runtime(
    nodes: List[RegexNode], node_index: Int, text: String, start: Int
) -> Optional[_MatchResult]:
    ref node = nodes[node_index]
    match node:
        case .Empty:
            return _MatchResult(0)
        case .Literal(ref literal):
            ref value = literal.value
            if start + value.byte_length() > text.byte_length():
                return None
            var text_bytes = text.as_bytes()
            var pattern_bytes = value.as_bytes()
            for i in range(value.byte_length()):
                if text_bytes[start + i] != pattern_bytes[i]:
                    return None
            return _MatchResult(value.byte_length())
        case .CharClass(ref char_class):
            var kind = char_class.kind
            if start >= text.byte_length():
                return None
            var value = Int(text.as_bytes()[start])
            if kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL:
                var span = text[byte = 0 : text.byte_length()]
                var width = _utf8_codepoint_width(span, start)
                if width == 0 or (
                    kind == CHAR_UNICODE_DOT and value == ord("\n")
                ):
                    return None
                return _MatchResult(width)
            if _runtime_class_accepts(kind, value):
                return _MatchResult(1)
            return None
        case .BracketClass(ref bracket):
            if start >= text.byte_length():
                return None
            var value = Int(text.as_bytes()[start])
            if _runtime_bracket_accepts(bracket, value):
                return _MatchResult(1)
            return None
        case .ZeroWidth(ref zero_width):
            var span = text[byte = 0 : text.byte_length()]
            return _MatchResult(0) if _zero_width_matches(
                zero_width.kind, span, start
            ) else None
        case .Or(ref alternation):
            for i in range(alternation.count):
                var result = _match_node_runtime(
                    nodes, alternation.options[i], text, start
                )
                if result:
                    return result^
            return None
        case .Repeat(ref repeat):
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
        case .Sequence(ref sequence):
            var consumed = 0
            for i in range(sequence.count):
                var result = _match_node_runtime(
                    nodes, sequence.items[i], text, start + consumed
                )
                if not result:
                    return None
                consumed += result.unsafe_value().consumed()
            return _MatchResult(consumed)
        case .Capture(ref capture):
            return _match_node_runtime(nodes, capture.child, text, start)


@no_inline
def matches_runtime(regex: Regex, text: String) -> Bool:
    """Reference AST interpreter used to quantify specialization overhead."""
    var result = _match_node_runtime(regex.nodes, regex.root, text, 0)
    return result and result.unsafe_value().consumed() == text.byte_length()
