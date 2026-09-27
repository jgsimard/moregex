"""Compile-time-planned executors for UTF-8 byte-class repetitions."""

from ._ast import (
    BracketClassNode,
    LiteralNode,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits
from std.utils import StaticTuple

from ._byte_predicates import _build_bracket_masks
from ._analysis import _node_start_accepts, _node_start_mask
from ._common import (
    CLASS_SIMD_WIDTH,
    _bracket_accepts,
    _match_checksum,
    _match_literal,
)


@always_inline
def _utf8_bracket_accepts[node: BracketClassNode](value: Int) -> Bool:
    """Test a byte class with a compact lookup for fragmented ranges."""
    comptime if node.count >= 3:
        comptime masks = _build_bracket_masks(node)
        if value < 64:
            return masks[0] & (UInt64(1) << UInt64(value)) != 0
        if value < 128:
            return masks[1] & (UInt64(1) << UInt64(value - 64)) != 0
        if value < 192:
            return masks[2] & (UInt64(1) << UInt64(value - 128)) != 0
        return masks[3] & (UInt64(1) << UInt64(value - 192)) != 0
    return _bracket_accepts[node](value)


def _same_byte_bracket[
    left: BracketClassNode, right: BracketClassNode
]() -> Bool:
    comptime if left.negated != right.negated or left.count != right.count:
        return False
    comptime for i in range(left.count):
        comptime if (
            left.lows[i] != right.lows[i] or left.highs[i] != right.highs[i]
        ):
            return False
    return True


def _is_utf8_byte_sequence[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if not node.isa[SequenceNode]():
        return False
    else:
        comptime sequence = node[SequenceNode]
        comptime if sequence.count < 2 or sequence.count > 4:
            return False
        comptime for i in range(sequence.count):
            comptime if not nodes[sequence.items[i]].isa[BracketClassNode]():
                return False
        return True


def _is_utf8_byte_class[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if not node.isa[OrNode]():
        return False
    else:
        comptime alternation = node[OrNode]
        comptime if alternation.count < 2:
            return False
        comptime for i in range(alternation.count):
            comptime option_index = alternation.options[i]
            comptime option = nodes[option_index]
            comptime if option.isa[BracketClassNode]():
                pass
            elif _is_utf8_byte_sequence[nodes, option_index]():
                pass
            else:
                return False
        comptime for i in range(alternation.count):
            comptime if _is_utf8_byte_sequence[nodes, alternation.options[i]]():
                return True
        return False


def _is_utf8_byte_class_repeat[
    nodes: List[RegexNode], root_index: Int
]() -> Bool:
    comptime root = nodes[root_index]
    comptime if not root.isa[RepeatNode]():
        return False
    else:
        comptime repeat = root[RepeatNode]
        return repeat.minimum > 0 and _is_utf8_byte_class[nodes, repeat.child]()


def _is_positive_utf8_repeat[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if not node.isa[RepeatNode]():
        return False
    else:
        comptime repeat = node[RepeatNode]
        return (
            repeat.minimum > 0
            and repeat.maximum < 0
            and _is_utf8_byte_class[nodes, repeat.child]()
        )


def _is_one_byte_separator[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[BracketClassNode]():
        return True
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for option in range(alternation.count):
            comptime if not nodes[alternation.options[option]].isa[
                BracketClassNode
            ]():
                return False
        return True
    return False


def _is_exact_utf8_class_sequence[
    nodes: List[RegexNode], root_index: Int
]() -> Bool:
    """Recognize exact UTF-8 class runs separated by one-byte classes."""
    comptime root = nodes[root_index]
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count < 3 or sequence.count % 2 == 0:
            return False
        comptime for item in range(sequence.count):
            comptime if item % 2 == 0:
                comptime node = nodes[sequence.items[item]]
                comptime if node.isa[RepeatNode]():
                    comptime repeat = node[RepeatNode]
                    comptime if (
                        repeat.minimum <= 0
                        or repeat.minimum != repeat.maximum
                        or not _is_utf8_byte_class[nodes, repeat.child]()
                    ):
                        return False
                else:
                    return False
            else:
                comptime if not _is_one_byte_separator[
                    nodes, sequence.items[item]
                ]():
                    return False
        return True
    return False


def _is_utf8_class_literal_infix_option[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    comptime node = nodes[node_index]
    comptime if not node.isa[SequenceNode]():
        return False
    else:
        comptime sequence = node[SequenceNode]
        comptime if sequence.count != 3:
            return False
        else:
            comptime middle = nodes[sequence.items[1]]
            return (
                middle.isa[LiteralNode]()
                and middle[LiteralNode].value.byte_length() > 0
                and _is_positive_utf8_repeat[nodes, sequence.items[0]]()
                and _is_positive_utf8_repeat[nodes, sequence.items[2]]()
            )


def _is_utf8_class_literal_infix_alternation[
    nodes: List[RegexNode], root_index: Int
]() -> Bool:
    comptime root = nodes[root_index]
    comptime if not root.isa[OrNode]():
        return False
    else:
        comptime alternation = root[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for i in range(alternation.count):
            comptime if not _is_utf8_class_literal_infix_option[
                nodes, alternation.options[i]
            ]():
                return False
        return True


def _is_utf8_class_separated_literal_infix[
    nodes: List[RegexNode], root_index: Int
]() -> Bool:
    """Recognize `utf8+ byte+ literal byte+ utf8+` sequences."""
    comptime root = nodes[root_index]
    comptime if not root.isa[SequenceNode]():
        return False
    else:
        comptime sequence = root[SequenceNode]
        comptime if sequence.count != 5:
            return False
        else:
            comptime literal = nodes[sequence.items[2]]
            comptime left_separator = nodes[sequence.items[1]]
            comptime right_separator = nodes[sequence.items[3]]
            comptime if (
                not literal.isa[LiteralNode]()
                or literal[LiteralNode].value.byte_length() == 0
                or not left_separator.isa[RepeatNode]()
                or not right_separator.isa[RepeatNode]()
            ):
                return False
            else:
                comptime left_repeat = left_separator[RepeatNode]
                comptime right_repeat = right_separator[RepeatNode]
                return (
                    _is_positive_utf8_repeat[nodes, sequence.items[0]]()
                    and _is_positive_utf8_repeat[nodes, sequence.items[4]]()
                    and left_repeat.greedy
                    and right_repeat.greedy
                    and left_repeat.minimum > 0
                    and right_repeat.minimum > 0
                    and left_repeat.maximum < 0
                    and right_repeat.maximum < 0
                    and _is_one_byte_separator[nodes, left_repeat.child]()
                    and _is_one_byte_separator[nodes, right_repeat.child]()
                )


def _bracket_is_below[bracket: BracketClassNode, limit: Int]() -> Bool:
    comptime if bracket.negated:
        return False
    comptime for i in range(bracket.count):
        comptime if bracket.highs[i] >= limit:
            return False
    return True


def _bracket_is_at_least[bracket: BracketClassNode, limit: Int]() -> Bool:
    comptime if bracket.negated:
        return False
    comptime for i in range(bracket.count):
        comptime if bracket.lows[i] < limit:
            return False
    return True


def _utf8_class_is_ascii_partitioned[
    nodes: List[RegexNode], alternation: OrNode
]() -> Bool:
    comptime for i in range(alternation.count):
        comptime option = nodes[alternation.options[i]]
        comptime if option.isa[BracketClassNode]():
            comptime if not _bracket_is_below[option[BracketClassNode], 128]():
                return False
        else:
            comptime sequence = option[SequenceNode]
            comptime first = nodes[sequence.items[0]][BracketClassNode]
            comptime if not _bracket_is_at_least[first, 128]():
                return False
    return True


def _utf8_class_max_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    comptime alternation = nodes[node_index][OrNode]
    var maximum = 1
    comptime for option in range(alternation.count):
        comptime node = nodes[alternation.options[option]]
        comptime if node.isa[SequenceNode]():
            maximum = max(maximum, node[SequenceNode].count)
    return maximum


def _utf8_ascii_masks[
    nodes: List[RegexNode], node_index: Int
]() -> StaticTuple[UInt64, 2]:
    """Build the accepted ASCII bytes for a normalized UTF-8 class."""
    var masks = StaticTuple[UInt64, 2]()
    comptime alternation = nodes[node_index][OrNode]
    comptime for option in range(alternation.count):
        comptime node = nodes[alternation.options[option]]
        comptime if node.isa[BracketClassNode]():
            comptime bracket = node[BracketClassNode]
            comptime for item in range(bracket.count):
                comptime for value in range(
                    bracket.lows[item], bracket.highs[item] + 1
                ):
                    comptime if value < 128:
                        masks[value >> 6] |= UInt64(1) << UInt64(value & 63)
    return masks


def _utf8_two_byte_suffix_masks[
    nodes: List[RegexNode], node_index: Int
]() -> StaticTuple[UInt64, 128]:
    """Build continuation-byte masks for UTF-8 leads 0xC0 through 0xDF."""
    var masks = StaticTuple[UInt64, 128]()
    comptime alternation = nodes[node_index][OrNode]
    comptime for option in range(alternation.count):
        comptime node = nodes[alternation.options[option]]
        comptime if node.isa[SequenceNode]():
            comptime sequence = node[SequenceNode]
            comptime if sequence.count == 2:
                comptime lead = nodes[sequence.items[0]][BracketClassNode]
                comptime suffix = nodes[sequence.items[1]][BracketClassNode]
                comptime for lead_item in range(lead.count):
                    comptime for lead_value in range(
                        lead.lows[lead_item], lead.highs[lead_item] + 1
                    ):
                        comptime if 0xC0 <= lead_value <= 0xDF:
                            comptime for suffix_item in range(suffix.count):
                                comptime for suffix_value in range(
                                    suffix.lows[suffix_item],
                                    suffix.highs[suffix_item] + 1,
                                ):
                                    comptime slot = (
                                        (lead_value - 0xC0) * 4
                                        + (suffix_value >> 6)
                                    )
                                    masks[slot] |= UInt64(1) << UInt64(
                                        suffix_value & 63
                                    )
    return masks


@always_inline
def _utf8_ascii_class_mask[
    nodes: List[RegexNode], node_index: Int, width: Int
](values: SIMD[.uint8, width]) -> SIMD[.bool, width]:
    """Merge the one-byte alternatives of a UTF-8 class for SIMD matching."""
    comptime alternation = nodes[node_index][OrNode]
    var accepted = SIMD[.bool, width](fill=False)
    comptime for option in range(alternation.count):
        comptime node = nodes[alternation.options[option]]
        comptime if node.isa[BracketClassNode]():
            accepted |= _node_start_mask[
                nodes, alternation.options[option], width
            ](values)
    return accepted


def _has_prior_sequence_prefix[
    nodes: List[RegexNode], alternation: OrNode, option_position: Int
]() -> Bool:
    comptime option = nodes[alternation.options[option_position]][SequenceNode]
    comptime first = nodes[option.items[0]][BracketClassNode]
    comptime for i in range(option_position):
        comptime prior = nodes[alternation.options[i]]
        comptime if prior.isa[SequenceNode]():
            comptime sequence = prior[SequenceNode]
            comptime prior_first = nodes[sequence.items[0]][BracketClassNode]
            comptime if _same_byte_bracket[first, prior_first]():
                return True
    return False


@always_inline
def _utf8_sequence_suffix_width[
    nodes: List[RegexNode], node_index: Int
](bytes: Span[Byte, _], start: Int) -> Int:
    comptime sequence = nodes[node_index][SequenceNode]
    if start + sequence.count > len(bytes):
        return 0
    var pointer = bytes.unsafe_ptr()
    comptime for i in range(1, sequence.count):
        comptime bracket = nodes[sequence.items[i]][BracketClassNode]
        if not _utf8_bracket_accepts[bracket](
            Int(pointer.unsafe_load(offset=start + i))
        ):
            return 0
    return sequence.count


@always_inline
def _utf8_byte_class_width[
    nodes: List[RegexNode], node_index: Int
](bytes: Span[Byte, _], start: Int) -> Int:
    if start >= len(bytes):
        return 0
    comptime alternation = nodes[node_index][OrNode]
    var value = Int(bytes.unsafe_ptr().unsafe_load(offset=start))
    comptime if _utf8_class_max_width[nodes, node_index]() == 2:
        if value < 128:
            comptime ascii_masks = _utf8_ascii_masks[nodes, node_index]()
            return (
                1 if ascii_masks[value >> 6] & (UInt64(1) << UInt64(value & 63))
                != 0 else 0
            )
        if value < 0xC0 or value > 0xDF or start + 1 >= len(bytes):
            return 0
        var suffix = Int(bytes.unsafe_ptr().unsafe_load(offset=start + 1))
        comptime suffix_masks = _utf8_two_byte_suffix_masks[nodes, node_index]()
        var slot = (value - 0xC0) * 4 + (suffix >> 6)
        return (
            2 if suffix_masks[slot] & (UInt64(1) << UInt64(suffix & 63))
            != 0 else 0
        )
    comptime if _utf8_class_is_ascii_partitioned[nodes, alternation]():
        if value < 128:
            comptime for i in range(alternation.count):
                comptime option = nodes[alternation.options[i]]
                comptime if option.isa[BracketClassNode]():
                    comptime bracket = option[BracketClassNode]
                    if _bracket_accepts[bracket](value):
                        return 1
            return 0
    comptime for i in range(alternation.count):
        comptime option_index = alternation.options[i]
        comptime option = nodes[option_index]
        comptime if option.isa[SequenceNode]():
            comptime if not _has_prior_sequence_prefix[nodes, alternation, i]():
                comptime sequence = option[SequenceNode]
                comptime first = nodes[sequence.items[0]][BracketClassNode]
                if _bracket_accepts[first](value):
                    comptime for j in range(i, alternation.count):
                        comptime candidate_index = alternation.options[j]
                        comptime candidate = nodes[candidate_index]
                        comptime if candidate.isa[SequenceNode]():
                            comptime candidate_sequence = candidate[
                                SequenceNode
                            ]
                            comptime candidate_first = nodes[
                                candidate_sequence.items[0]
                            ][BracketClassNode]
                            comptime if _same_byte_bracket[
                                first, candidate_first
                            ]():
                                var width = _utf8_sequence_suffix_width[
                                    nodes, candidate_index
                                ](bytes, start)
                                if width > 0:
                                    return width
        elif not _utf8_class_is_ascii_partitioned[nodes, alternation]():
            comptime bracket = option[BracketClassNode]
            if _bracket_accepts[bracket](value):
                return 1
    return 0


@always_inline
def _count_utf8_byte_class_repeat[
    regex: Regex, sum_spans: Bool
](bytes: Span[Byte, _]) -> Int:
    comptime repeat = regex.nodes[regex.root][RepeatNode]
    var position = 0
    var total = 0
    comptime if not sum_spans and repeat.maximum > 0:
        while position < len(bytes):
            var width = _utf8_byte_class_width[regex.nodes, repeat.child](
                bytes, position
            )
            if width == 0:
                position += 1
                continue
            var count = 0
            while width > 0:
                count += 1
                position += width
                if count == repeat.maximum:
                    total += 1
                    count = 0
                width = _utf8_byte_class_width[regex.nodes, repeat.child](
                    bytes, position
                )
            if count >= repeat.minimum:
                total += 1
        return total
    while position < len(bytes):
        var width = _utf8_byte_class_width[regex.nodes, repeat.child](
            bytes, position
        )
        if width == 0:
            position += 1
            continue
        var consumed = 0
        var count = 0
        while width > 0 and (repeat.maximum < 0 or count < repeat.maximum):
            consumed += width
            count += 1
            position += width
            width = _utf8_byte_class_width[regex.nodes, repeat.child](
                bytes, position
            )
        if count >= repeat.minimum:
            total += _match_checksum[sum_spans](consumed)
    return total


@fieldwise_init
struct _Utf8InfixMatch(TrivialRegisterPassable):
    var start: Int
    var end: Int


def _utf8_infix_max_literal_length[regex: Regex]() -> Int:
    comptime alternation = regex.nodes[regex.root][OrNode]
    var maximum = 1
    comptime for option in range(alternation.count):
        comptime sequence = regex.nodes[alternation.options[option]][
            SequenceNode
        ]
        comptime literal = regex.nodes[sequence.items[1]][LiteralNode]
        maximum = max(maximum, literal.value.byte_length())
    return maximum


@always_inline
def _match_utf8_class_literal_infix_option_at[
    regex: Regex, option_index: Int
](text: ImmStringSpan, candidate: Int, search_start: Int) -> Optional[
    _Utf8InfixMatch
]:
    comptime sequence = regex.nodes[option_index][SequenceNode]
    comptime left = regex.nodes[sequence.items[0]][RepeatNode]
    comptime literal = regex.nodes[sequence.items[1]][LiteralNode]
    comptime right = regex.nodes[sequence.items[2]][RepeatNode]
    if not _match_literal[literal.value](text, candidate):
        return None
    var bytes = text.as_bytes()
    var start = candidate
    var left_count = 0
    while start > search_start:
        var width = _previous_utf8_class_width[regex.nodes, left.child](
            bytes, start, search_start
        )
        if width == 0:
            break
        start -= width
        left_count += 1
    var end = candidate + literal.value.byte_length()
    var right_count = 0
    while end < len(bytes):
        var width = _utf8_byte_class_width[regex.nodes, right.child](bytes, end)
        if width == 0:
            break
        end += width
        right_count += 1
    if left_count >= left.minimum and right_count >= right.minimum:
        return _Utf8InfixMatch(start, end)
    return None


@always_inline
def _previous_utf8_class_width[
    nodes: List[RegexNode], class_index: Int
](bytes: Span[Byte, _], end: Int, minimum: Int) -> Int:
    comptime for width in range(1, 5):
        if (
            end - width >= minimum
            and _utf8_byte_class_width[nodes, class_index](bytes, end - width)
            == width
        ):
            return width
    return 0


@always_inline
def _exact_utf8_class_sequence_at_separator[
    regex: Regex
](bytes: Span[Byte, _], separator: Int, minimum_start: Int) -> Tuple[Int, Int]:
    """Return a match span around the first separator, or `(-1, -1)`."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime first = regex.nodes[sequence.items[0]][RepeatNode]
    var start = separator
    comptime for _ in range(first.minimum):
        var width = _previous_utf8_class_width[regex.nodes, first.child](
            bytes, start, minimum_start
        )
        if width == 0:
            return (-1, -1)
        start -= width

    # The caller selected `separator` from the first separator AST node.
    var end = separator + 1
    comptime for item in range(2, sequence.count):
        comptime if item % 2 == 1:
            if end >= len(bytes) or not _node_start_accepts[
                regex.nodes, sequence.items[item]
            ](Int(bytes[end])):
                return (-1, -1)
            end += 1
        else:
            comptime repeat = regex.nodes[sequence.items[item]][RepeatNode]
            comptime for _ in range(repeat.minimum):
                var width = _utf8_byte_class_width[regex.nodes, repeat.child](
                    bytes, end
                )
                if width == 0:
                    return (-1, -1)
                end += width
    return (start, end)


def _exact_utf8_separator_extents[regex: Regex]() -> Tuple[Int, Int]:
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime first = regex.nodes[sequence.items[0]][RepeatNode]
    var prefix = (
        first.minimum * _utf8_class_max_width[regex.nodes, first.child]()
    )
    var suffix = 1
    comptime for item in range(2, sequence.count):
        comptime if item % 2 == 1:
            suffix += 1
        else:
            comptime repeat = regex.nodes[sequence.items[item]][RepeatNode]
            suffix += (
                repeat.minimum
                * _utf8_class_max_width[regex.nodes, repeat.child]()
            )
    return (prefix, suffix)


@always_inline
def _exact_utf8_ascii_separator_mask[
    regex: Regex, width: Int
](bytes: Span[Byte, _], separator: Int) -> SIMD[.bool, width]:
    """Match the all-ASCII form at positions of its first separator."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime first = regex.nodes[sequence.items[0]][RepeatNode]
    var pointer = bytes.unsafe_ptr()
    var matched = _node_start_mask[regex.nodes, sequence.items[1], width](
        pointer.unsafe_load[width=width, alignment=1](separator)
    )
    comptime for repetition in range(first.minimum):
        var values = pointer.unsafe_load[width=width, alignment=1](
            separator - first.minimum + repetition
        )
        matched &= _utf8_ascii_class_mask[regex.nodes, first.child, width](
            values
        )
    var position = 1
    comptime for item in range(2, sequence.count):
        comptime if item % 2 == 1:
            var values = pointer.unsafe_load[width=width, alignment=1](
                separator + position
            )
            matched &= _node_start_mask[
                regex.nodes, sequence.items[item], width
            ](values)
            position += 1
        else:
            comptime repeat = regex.nodes[sequence.items[item]][RepeatNode]
            comptime for _ in range(repeat.minimum):
                var values = pointer.unsafe_load[width=width, alignment=1](
                    separator + position
                )
                matched &= _utf8_ascii_class_mask[
                    regex.nodes, repeat.child, width
                ](values)
                position += 1
    return matched


@always_inline
def _count_exact_utf8_class_sequence[
    regex: Regex, sum_spans: Bool
](bytes: Span[Byte, _]) -> Int:
    """Count an exact UTF-8 class sequence from SIMD separator candidates."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime separator_index = sequence.items[1]
    var total = 0
    var next_start = 0
    comptime extents = _exact_utf8_separator_extents[regex]()
    comptime maximum_prefix = extents[0]
    comptime maximum_suffix = extents[1]
    var offset = 0
    var pointer = bytes.unsafe_ptr()
    while offset < min(maximum_prefix, len(bytes)):
        if _node_start_accepts[regex.nodes, separator_index](
            Int(bytes[offset])
        ):
            var matched = _exact_utf8_class_sequence_at_separator[regex](
                bytes, offset, next_start
            )
            if matched[0] >= next_start:
                total += _match_checksum[sum_spans](matched[1] - matched[0])
                next_start = matched[1]
        offset += 1

    while offset + CLASS_SIMD_WIDTH + maximum_suffix <= len(bytes):
        var values = pointer.unsafe_load[width=CLASS_SIMD_WIDTH, alignment=1](
            offset
        )
        var separators = _node_start_mask[
            regex.nodes, separator_index, CLASS_SIMD_WIDTH
        ](values)
        var candidates = _exact_utf8_ascii_separator_mask[
            regex, CLASS_SIMD_WIDTH
        ](bytes, offset)
        var near_non_ascii = SIMD[.bool, CLASS_SIMD_WIDTH](fill=False)
        for displacement in range(-maximum_prefix, maximum_suffix):
            var nearby = pointer.unsafe_load[
                width=CLASS_SIMD_WIDTH, alignment=1
            ](offset + displacement)
            near_non_ascii |= nearby.ge(128)
        candidates |= separators & near_non_ascii
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var matched = _exact_utf8_class_sequence_at_separator[regex](
                bytes, offset + lane, next_start
            )
            if matched[0] >= next_start:
                total += _match_checksum[sum_spans](matched[1] - matched[0])
                next_start = matched[1]
        offset += CLASS_SIMD_WIDTH

    while offset < len(bytes):
        if _node_start_accepts[regex.nodes, separator_index](
            Int(bytes[offset])
        ):
            var matched = _exact_utf8_class_sequence_at_separator[regex](
                bytes, offset, next_start
            )
            if matched[0] >= next_start:
                total += _match_checksum[sum_spans](matched[1] - matched[0])
                next_start = matched[1]
        offset += 1
    return total


@always_inline
def _count_utf8_class_separated_literal_infix[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count UTF-8 word-like runs around a separated mandatory literal."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime left = regex.nodes[sequence.items[0]][RepeatNode]
    comptime left_separator = regex.nodes[sequence.items[1]][RepeatNode]
    comptime literal = regex.nodes[sequence.items[2]][LiteralNode]
    comptime right_separator = regex.nodes[sequence.items[3]][RepeatNode]
    comptime right = regex.nodes[sequence.items[4]][RepeatNode]
    var bytes = text.as_bytes()
    var length = len(bytes)
    var total = 0
    var minimum_start = 0
    var candidate = text.find(literal.value)
    while candidate >= 0:
        var separator_start = candidate
        var separator_count = 0
        while separator_start > minimum_start and _node_start_accepts[
            regex.nodes, left_separator.child
        ](Int(bytes[separator_start - 1])):
            separator_start -= 1
            separator_count += 1
        var start = separator_start
        var left_count = 0
        if separator_count >= left_separator.minimum:
            while start > minimum_start:
                var width = _previous_utf8_class_width[regex.nodes, left.child](
                    bytes, start, minimum_start
                )
                if width == 0:
                    break
                start -= width
                left_count += 1

        var end = candidate + literal.value.byte_length()
        var right_separator_count = 0
        while end < length and _node_start_accepts[
            regex.nodes, right_separator.child
        ](Int(bytes[end])):
            end += 1
            right_separator_count += 1
        var right_count = 0
        if right_separator_count >= right_separator.minimum:
            while end < length:
                var width = _utf8_byte_class_width[regex.nodes, right.child](
                    bytes, end
                )
                if width == 0:
                    break
                end += width
                right_count += 1

        if (
            separator_count >= left_separator.minimum
            and left_count >= left.minimum
            and right_separator_count >= right_separator.minimum
            and right_count >= right.minimum
        ):
            total += _match_checksum[sum_spans](end - start)
            minimum_start = end
            candidate = text.find(literal.value, minimum_start)
        else:
            candidate = text.find(literal.value, candidate + 1)
    return total


@always_inline
def _count_utf8_class_literal_infix_alternation[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    comptime alternation = regex.nodes[regex.root][OrNode]
    comptime maximum_literal_length = _utf8_infix_max_literal_length[regex]()
    var length = text.byte_length()
    var search_start = 0
    var total = 0
    var offset = 0
    var pointer = text.unsafe_ptr()
    while offset + CLASS_SIMD_WIDTH + maximum_literal_length - 1 <= length:
        var first_values = pointer.unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](offset)
        var candidates = SIMD[.bool, CLASS_SIMD_WIDTH](fill=False)
        comptime for i in range(alternation.count):
            comptime sequence = regex.nodes[alternation.options[i]][
                SequenceNode
            ]
            comptime literal = regex.nodes[sequence.items[1]][LiteralNode]
            comptime last = literal.value.byte_length() - 1
            var last_values = pointer.unsafe_load[
                width=CLASS_SIMD_WIDTH, alignment=1
            ](offset + last)
            candidates |= first_values.eq(
                SIMD[.uint8, CLASS_SIMD_WIDTH](literal.value.as_bytes()[0])
            ) & last_values.eq(
                SIMD[.uint8, CLASS_SIMD_WIDTH](literal.value.as_bytes()[last])
            )
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var candidate = offset + lane
            if candidate < search_start:
                continue
            var matched_end = -1
            var matched_start = -1
            comptime for i in range(alternation.count):
                if matched_end < 0:
                    var found = _match_utf8_class_literal_infix_option_at[
                        regex, alternation.options[i]
                    ](text, candidate, search_start)
                    if found:
                        var matched = found.unsafe_value()
                        matched_start = matched.start
                        matched_end = matched.end
            if matched_end >= 0:
                total += _match_checksum[sum_spans](matched_end - matched_start)
                search_start = matched_end
        offset += CLASS_SIMD_WIDTH

    while offset < length:
        if offset >= search_start:
            var matched_end = -1
            var matched_start = -1
            comptime for i in range(alternation.count):
                if matched_end < 0:
                    var found = _match_utf8_class_literal_infix_option_at[
                        regex, alternation.options[i]
                    ](text, offset, search_start)
                    if found:
                        var matched = found.unsafe_value()
                        matched_start = matched.start
                        matched_end = matched.end
            if matched_end >= 0:
                total += _match_checksum[sum_spans](matched_end - matched_start)
                search_start = matched_end
        offset += 1
    return total
