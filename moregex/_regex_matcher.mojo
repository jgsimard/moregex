"""Generic compile-time AST matcher."""

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
from ._regex_common import (
    _MatchResult,
    _bracket_accepts,
    _match_class,
    _match_literal,
    _matches_class_run,
    _static_source_is_root_literal,
    _zero_width_matches,
)

from ._regex_masks import _build_bracket_masks
from ._regex_analysis import (
    _fixed_node_width,
)
from ._regex_nfa import _nfa_full_match
from ._regex_semantics import _nfa_full_semantics_required


@always_inline
def _match_sequence_from[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
](text: ImmStringSpan, start: Int) -> Optional[_MatchResult]:
    comptime if item == sequence.count:
        return _MatchResult(0)
    else:
        comptime child_index = sequence.items[item]
        comptime child = nodes[child_index]
        comptime if child.isa[OrNode]():
            comptime alternation = child[OrNode]
            comptime for option in range(alternation.count):
                var alternative = _match_node[
                    nodes, alternation.options[option]
                ](text, start)
                if alternative:
                    var alternative_length = (
                        alternative.unsafe_value().consumed()
                    )
                    var suffix = _match_sequence_from[
                        nodes, sequence, item + 1
                    ](text, start + alternative_length)
                    if suffix:
                        return _MatchResult(
                            alternative_length
                            + suffix.unsafe_value().consumed()
                        )
            return None
        comptime if child.isa[RepeatNode]():
            comptime repeat = child[RepeatNode]
            comptime child_width = _fixed_node_width[nodes, repeat.child]()
            comptime if child_width > 0:
                comptime if not repeat.greedy:
                    var lazy_count = 0
                    var lazy_consumed = 0
                    while lazy_count < repeat.minimum:
                        var required = _match_node[nodes, repeat.child](
                            text, start + lazy_consumed
                        )
                        if not required:
                            return None
                        lazy_count += 1
                        lazy_consumed += child_width

                    while True:
                        var lazy_suffix = _match_sequence_from[
                            nodes, sequence, item + 1
                        ](text, start + lazy_consumed)
                        if lazy_suffix:
                            return _MatchResult(
                                lazy_consumed
                                + lazy_suffix.unsafe_value().consumed()
                            )
                        comptime if repeat.maximum >= 0:
                            if lazy_count >= repeat.maximum:
                                break
                        var next = _match_node[nodes, repeat.child](
                            text, start + lazy_consumed
                        )
                        if not next:
                            break
                        lazy_count += 1
                        lazy_consumed += child_width
                    return None

                var count = 0
                var consumed = 0
                while True:
                    comptime if repeat.maximum >= 0:
                        if count >= repeat.maximum:
                            break
                    var result = _match_node[nodes, repeat.child](
                        text, start + consumed
                    )
                    if not result:
                        break
                    count += 1
                    consumed += child_width

                while count >= repeat.minimum:
                    var suffix = _match_sequence_from[
                        nodes, sequence, item + 1
                    ](text, start + consumed)
                    if suffix:
                        return _MatchResult(
                            consumed + suffix.unsafe_value().consumed()
                        )
                    count -= 1
                    consumed -= child_width
                return None

        var result = _match_node[nodes, child_index](text, start)
        if not result:
            return None
        var suffix = _match_sequence_from[nodes, sequence, item + 1](
            text, start + result.unsafe_value().consumed()
        )
        if not suffix:
            return None
        return _MatchResult(
            result.unsafe_value().consumed() + suffix.unsafe_value().consumed()
        )


@always_inline
def _match_node[
    nodes: List[RegexNode], node_index: Int
](text: ImmStringSpan, start: Int) -> Optional[_MatchResult]:
    comptime node = nodes[node_index]
    comptime if node.isa[EmptyNode]():
        return _MatchResult(0)
    elif node.isa[LiteralNode]():
        comptime literal = node[LiteralNode]
        return _match_literal[literal.value](text, start)
    elif node.isa[CharClassNode]():
        comptime char_class = node[CharClassNode]
        return _match_class[char_class.kind](text, start)
    elif node.isa[BracketClassNode]():
        comptime bracket = node[BracketClassNode]
        if start >= text.byte_length():
            return None
        var value = Int(text.as_bytes()[start])
        comptime if bracket.count >= 3:
            comptime masks = _build_bracket_masks(bracket)
            var bit = UInt64(1) << UInt64(value % 64)
            return _MatchResult(1) if masks[value // 64] & bit != 0 else None
        return _MatchResult(1) if _bracket_accepts[bracket](value) else None
    elif node.isa[ZeroWidthNode]():
        comptime zero_width = node[ZeroWidthNode]
        return _MatchResult(0) if _zero_width_matches(
            zero_width.kind, text, start
        ) else None
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime for i in range(alternation.count):
            var result = _match_node[nodes, alternation.options[i]](text, start)
            if result:
                return result^
        return None
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        var count = 0
        var consumed = 0
        while True:
            comptime if not repeat.greedy:
                if count >= repeat.minimum:
                    break
            comptime if repeat.maximum >= 0:
                if count >= repeat.maximum:
                    break
            var result = _match_node[nodes, repeat.child](
                text, start + consumed
            )
            if not result or result.unsafe_value().consumed() == 0:
                break
            count += 1
            consumed += result.unsafe_value().consumed()
        if count >= repeat.minimum:
            return _MatchResult(consumed)
        return None
    else:
        comptime sequence = node[SequenceNode]
        return _match_sequence_from[nodes, sequence, 0](text, start)


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
