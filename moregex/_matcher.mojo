"""Generic compile-time AST matcher."""

from ._ast import (
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
    CharClassNode,
    LiteralNode,
    RepeatNode,
)
from ._syntax import Regex, _static_source_is_root_literal
from ._common import (
    _match_literal,
    _matches_class_run,
)
from ._nfa import _nfa_full_match
from ._semantics import _nfa_full_semantics_required

from ._ast_matcher import _match_node


@always_inline
def _matches_span_impl[regex: Regex](text: ImmStringSpan) -> Bool:
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[RepeatNode]():
        comptime repeat = root[RepeatNode]
        comptime child = regex.nodes[repeat.child]
        comptime if (
            repeat.minimum == 1
            and repeat.maximum == -1
            and child.isa[CharClassNode]()
        ):
            comptime char_class = child[CharClassNode]
            comptime if (
                char_class.kind < CHAR_UNICODE_DOT
                or char_class.kind > CHAR_UNICODE_DOTALL
            ):
                return _matches_class_run[char_class.kind](text)
    var result = _match_node[regex.nodes, regex.root](text, 0)
    if result and result.unsafe_value().consumed() == text.byte_length():
        return True
    comptime if _nfa_full_semantics_required(regex.nodes, regex.root):
        return _nfa_full_match[regex](text)
    return False


@always_inline
def matches_span[regex: Regex](text: ImmStringSpan) -> Bool:
    """Return whether borrowed text is a full match."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        comptime literal = root[LiteralNode]
        if text.byte_length() != literal.value.byte_length():
            return False
        var result = _match_literal[literal.value](text, 0)
        return Bool(result)
    return _matches_span_impl[regex](text)


@always_inline
def matches[regex: Regex](text: String) -> Bool:
    """Return whether text is a full match for a compile-time regex."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        comptime literal = root[LiteralNode]
        comptime literal_length = literal.value.byte_length()
        if text.byte_length() != literal_length:
            return False
        comptime if literal_length == 0:
            return True
        comptime first = Int(literal.value.as_bytes()[0])
        comptime last = Int(literal.value.as_bytes()[literal_length - 1])
        var text_bytes = text.as_bytes()
        if (
            Int(text_bytes[0]) != first
            or Int(text_bytes[literal_length - 1]) != last
        ):
            return False
        comptime if _static_source_is_root_literal[regex]():
            return text == regex.source
        return text == literal.value
    return _matches_span_impl[regex](text[byte = 0 : text.byte_length()])
