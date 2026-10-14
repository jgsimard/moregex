"""Generic compile-time AST matcher."""

from ._width import _fixed_node_width
from ._ast import RegexNode, SequenceNode
from ._common import (
    _MatchResult,
    _bracket_accepts,
    _match_class,
    _match_literal,
    _zero_width_matches,
)

from ._byte_predicates import _build_bracket_masks


@always_inline
def _match_sequence_from[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
](text: ImmStringSpan, start: Int) -> Optional[_MatchResult]:
    comptime if item == sequence.count:
        return _MatchResult(0)
    else:
        comptime child_index = sequence.items[item]
        comptime child = nodes[child_index]
        comptime match child:
            case .Or(alternation):
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
            case .Repeat(repeat):
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
            case _:
                pass

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
    comptime match node:
        case .Empty:
            return _MatchResult(0)
        case .Literal(literal):
            return _match_literal[literal.value](text, start)
        case .CharClass(char_class):
            return _match_class[char_class.kind](text, start)
        case .BracketClass(bracket):
            if start >= text.byte_length():
                return None
            var value = Int(text.as_bytes()[start])
            comptime if bracket.count >= 3:
                comptime masks = _build_bracket_masks(bracket)
                var bit = UInt64(1) << UInt64(value % 64)
                return (
                    _MatchResult(1) if masks[value // 64] & bit != 0 else None
                )
            return _MatchResult(1) if _bracket_accepts[bracket](value) else None
        case .ZeroWidth(zero_width):
            return _MatchResult(0) if _zero_width_matches(
                zero_width.kind, text, start
            ) else None
        case .Or(alternation):
            comptime for i in range(alternation.count):
                var result = _match_node[nodes, alternation.options[i]](
                    text, start
                )
                if result:
                    return result^
            return None
        case .Repeat(repeat):
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
        case .Sequence(sequence):
            return _match_sequence_from[nodes, sequence, 0](text, start)
        case .Capture(capture):
            return _match_node[nodes, capture.child](text, start)
