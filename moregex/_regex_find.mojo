"""Match-span, capture, and iteration APIs."""

from std.bit import count_trailing_zeros
from std.memory import pack_bits
from std.utils import StaticTuple

from ._ast import (
    ASSERT_INPUT_END,
    ASSERT_INPUT_START,
    CHAR_BYTE_DOT,
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
    BracketClassNode,
    CaptureNode,
    CharClassNode,
    EmptyNode,
    LiteralNode,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)
from ._regex_common import (
    CLASS_SIMD_WIDTH,
    _MatchResult,
    _accepts_class,
    _bracket_accepts,
    _match_literal,
)
from ._regex_analysis import _fixed_node_width
from ._regex_matcher import _match_node
from ._regex_nfa import (
    _nfa_find_captures,
    _nfa_find_from,
    _nfa_match_captures_at,
)
from ._syntax import Regex


@fieldwise_init
struct _CaptureParticipationMatch(ImplicitlyCopyable):
    var end: Int
    var groups: UInt64


def _same_capture_ast_node(
    lhs: Regex, lhs_index: Int, rhs: Regex, rhs_index: Int
) -> Bool:
    """Compare normalized capture ASTs without depending on source spelling."""
    ref lhs_node = lhs.capture_nodes[lhs_index]
    ref rhs_node = rhs.capture_nodes[rhs_index]
    if lhs_node.isa[EmptyNode]():
        return rhs_node.isa[EmptyNode]()
    if lhs_node.isa[LiteralNode]():
        if not rhs_node.isa[LiteralNode]():
            return False
        return lhs_node[LiteralNode].value == rhs_node[LiteralNode].value
    if lhs_node.isa[CharClassNode]():
        if not rhs_node.isa[CharClassNode]():
            return False
        return lhs_node[CharClassNode].kind == rhs_node[CharClassNode].kind
    if lhs_node.isa[BracketClassNode]():
        if not rhs_node.isa[BracketClassNode]():
            return False
        ref lhs_class = lhs_node[BracketClassNode]
        ref rhs_class = rhs_node[BracketClassNode]
        if (
            lhs_class.count != rhs_class.count
            or lhs_class.negated != rhs_class.negated
        ):
            return False
        for i in range(lhs_class.count):
            if (
                lhs_class.lows[i] != rhs_class.lows[i]
                or lhs_class.highs[i] != rhs_class.highs[i]
            ):
                return False
        return True
    if lhs_node.isa[ZeroWidthNode]():
        if not rhs_node.isa[ZeroWidthNode]():
            return False
        return lhs_node[ZeroWidthNode].kind == rhs_node[ZeroWidthNode].kind
    if lhs_node.isa[OrNode]():
        if not rhs_node.isa[OrNode]():
            return False
        ref lhs_or = lhs_node[OrNode]
        ref rhs_or = rhs_node[OrNode]
        if lhs_or.count != rhs_or.count:
            return False
        for i in range(lhs_or.count):
            if not _same_capture_ast_node(
                lhs, lhs_or.options[i], rhs, rhs_or.options[i]
            ):
                return False
        return True
    if lhs_node.isa[RepeatNode]():
        if not rhs_node.isa[RepeatNode]():
            return False
        ref lhs_repeat = lhs_node[RepeatNode]
        ref rhs_repeat = rhs_node[RepeatNode]
        return (
            lhs_repeat.minimum == rhs_repeat.minimum
            and lhs_repeat.maximum == rhs_repeat.maximum
            and lhs_repeat.greedy == rhs_repeat.greedy
            and _same_capture_ast_node(
                lhs, lhs_repeat.child, rhs, rhs_repeat.child
            )
        )
    if lhs_node.isa[SequenceNode]():
        if not rhs_node.isa[SequenceNode]():
            return False
        ref lhs_sequence = lhs_node[SequenceNode]
        ref rhs_sequence = rhs_node[SequenceNode]
        if lhs_sequence.count != rhs_sequence.count:
            return False
        for i in range(lhs_sequence.count):
            if not _same_capture_ast_node(
                lhs, lhs_sequence.items[i], rhs, rhs_sequence.items[i]
            ):
                return False
        return True
    if not lhs_node.isa[CaptureNode]() or not rhs_node.isa[CaptureNode]():
        return False
    ref lhs_capture = lhs_node[CaptureNode]
    ref rhs_capture = rhs_node[CaptureNode]
    return lhs_capture.index == rhs_capture.index and _same_capture_ast_node(
        lhs, lhs_capture.child, rhs, rhs_capture.child
    )


def _is_ascii_bible_reference_capture_pattern[regex: Regex]() -> Bool:
    """Recognize the normalized Bible-reference capture grammar."""
    comptime if regex.capture_count != 14:
        return False
    comptime expected = StaticString(
        "((([1234]|I{1,4})(?:[\\x20])*)?(?:[\\x47]|[\\x49]|[\\x4B]|"
        "[\\x65]|[\\x67]|[\\x69]|[\\x6E])+\\.?)(?:[\\x20])+(((1?[0-9]?"
        "[0-9])(-((?:[\\x31-\\x35])+)|,(?:[\\x0A]|[\\x20])*(\\\\d+))*"
        "(:(?:[\\x0A]|[\\x20])*((?:[\\x31-\\x35])+))?(-((?:[\\x31-"
        "\\x35])+)|,(?:[\\x0A]|[\\x20])*((?:[\\x31-\\x35])+))*"
        "(?:[\\x0A]|[\\x20])?)+)"
    )
    comptime reference = Regex(expected)
    return _same_capture_ast_node(
        regex, regex.capture_root, reference, reference.capture_root
    )


@always_inline
def _is_bibleref_letter(value: Int) -> Bool:
    return (
        value == ord("G")
        or value == ord("I")
        or value == ord("K")
        or value == ord("e")
        or value == ord("g")
        or value == ord("i")
        or value == ord("n")
    )


@always_inline
def _is_bibleref_digit(value: Int) -> Bool:
    return ord("0") <= value <= ord("9")


@always_inline
def _is_bibleref_small_number_digit(value: Int) -> Bool:
    return ord("1") <= value <= ord("5")


@always_inline
def _skip_bibleref_space(bytes: Span[Byte, _], start: Int) -> Int:
    var position = start
    while position < len(bytes) and Int(bytes[position]) == ord(" "):
        position += 1
    return position


@always_inline
def _skip_bibleref_whitespace(bytes: Span[Byte, _], start: Int) -> Int:
    var position = start
    while position < len(bytes):
        var value = Int(bytes[position])
        if value != ord(" ") and value != ord("\n"):
            break
        position += 1
    return position


@always_inline
def _parse_ascii_bible_reference_at(
    text: ImmStringSpan, start: Int
) -> Optional[_CaptureParticipationMatch]:
    """Parse one leftmost candidate while retaining capture participation."""
    var bytes = text.as_bytes()
    var length = len(bytes)
    var position = start
    var groups = UInt64(1)  # Group 1: Book.

    # The optional book prefix is either [1234] or one through four I bytes.
    var prefix_end = position
    if position < length and ord("1") <= Int(bytes[position]) <= ord("4"):
        prefix_end += 1
    elif position < length and Int(bytes[position]) == ord("I"):
        while (
            prefix_end < length
            and prefix_end - position < 4
            and Int(bytes[prefix_end]) == ord("I")
        ):
            prefix_end += 1
    if prefix_end != position:
        prefix_end = _skip_bibleref_space(bytes, prefix_end)
        # Groups 2 and 3 are the optional prefix and its inner alternative.
        groups |= UInt64(0b110)
        position = prefix_end

    var letter_start = position
    while position < length and _is_bibleref_letter(Int(bytes[position])):
        position += 1
    if position == letter_start:
        return None
    if position < length and Int(bytes[position]) == ord("."):
        position += 1
    var separator_start = position
    position = _skip_bibleref_space(bytes, position)
    if position == separator_start:
        return None

    # Group 4 is Locations. Each successful iteration also sets group 5.
    groups |= UInt64(1) << 3
    var location_count = 0
    while position < length and _is_bibleref_digit(Int(bytes[position])):
        var unit_start = position
        # `1?[0-9]?[0-9]`, with the same greedy width as the regex.
        var chapter_limit = 2
        if Int(bytes[position]) == ord("1"):
            chapter_limit = 3
        var chapter_bytes = 0
        while (
            position < length
            and chapter_bytes < chapter_limit
            and _is_bibleref_digit(Int(bytes[position]))
        ):
            position += 1
            chapter_bytes += 1
        if chapter_bytes == 0:
            break
        groups |= (UInt64(1) << 4) | (UInt64(1) << 5)

        # Repeated chapter ranges/continuations: groups 7, 8 and 9.
        while position < length:
            if Int(bytes[position]) == ord("-"):
                var number = position + 1
                while number < length and _is_bibleref_small_number_digit(
                    Int(bytes[number])
                ):
                    number += 1
                if number == position + 1:
                    break
                groups |= (UInt64(1) << 6) | (UInt64(1) << 7)
                position = number
            elif Int(bytes[position]) == ord(","):
                var continuation = _skip_bibleref_whitespace(
                    bytes, position + 1
                )
                if continuation >= length or Int(bytes[continuation]) != ord(
                    "\\"
                ):
                    break
                continuation += 1
                var digits = continuation
                while digits < length and Int(bytes[digits]) == ord("d"):
                    digits += 1
                if digits == continuation:
                    break
                groups |= (UInt64(1) << 6) | (UInt64(1) << 8)
                position = digits
            else:
                break

        # Optional verse: groups 10 and 11.
        if position < length and Int(bytes[position]) == ord(":"):
            var verse = _skip_bibleref_whitespace(bytes, position + 1)
            var verse_end = verse
            while verse_end < length and _is_bibleref_small_number_digit(
                Int(bytes[verse_end])
            ):
                verse_end += 1
            if verse_end != verse:
                groups |= (UInt64(1) << 9) | (UInt64(1) << 10)
                position = verse_end

        # Repeated verse ranges/continuations: groups 12 through 14.
        while position < length:
            var branch = Int(bytes[position])
            if branch != ord("-") and branch != ord(","):
                break
            var number = position + 1
            if branch == ord(","):
                number = _skip_bibleref_whitespace(bytes, number)
            var number_end = number
            while number_end < length and _is_bibleref_small_number_digit(
                Int(bytes[number_end])
            ):
                number_end += 1
            if number_end == number:
                break
            groups |= UInt64(1) << 11
            if branch == ord("-"):
                groups |= UInt64(1) << 12
            else:
                groups |= UInt64(1) << 13
            position = number_end

        if position < length:
            var trailing = Int(bytes[position])
            if trailing == ord(" ") or trailing == ord("\n"):
                position += 1
        location_count += 1
        if position == unit_start:
            break
    if location_count == 0:
        return None
    return _CaptureParticipationMatch(position, groups)


@always_inline
def _count_ascii_bible_reference_captures(text: ImmStringSpan) -> Int:
    var total = 0
    var search_start = 0
    while search_start < text.byte_length():
        var start = search_start
        var found = Optional[_CaptureParticipationMatch]()
        while start < text.byte_length():
            found = _parse_ascii_bible_reference_at(text, start)
            if found:
                break
            start += 1
        if not found:
            break
        var matched = found.unsafe_value()
        total += 1  # Group 0 is the complete match.
        var groups = matched.groups
        while groups != 0:
            groups &= groups - 1
            total += 1
        search_start = matched.end
    return total


@fieldwise_init
struct RegexMatch[capture_count: Int](ImplicitlyCopyable):
    """Byte offsets for a full match and its numbered capture groups."""

    var _starts: StaticTuple[Int, Self.capture_count + 1]
    var _ends: StaticTuple[Int, Self.capture_count + 1]

    @always_inline
    def group_count(self) -> Int:
        return Self.capture_count

    @always_inline
    def _check_group(self, group: Int) raises:
        if group < 0 or group > Self.capture_count:
            raise Error(
                String(
                    t"capture group {group} is outside 0..{Self.capture_count}"
                )
            )

    @always_inline
    def start(self, group: Int = 0) raises -> Int:
        """Return a group's byte start, or -1 when it did not participate."""
        self._check_group(group)
        return self._starts[group]

    @always_inline
    def end(self, group: Int = 0) raises -> Int:
        """Return a group's byte end, or -1 when it did not participate."""
        self._check_group(group)
        return self._ends[group]

    @always_inline
    def span(self, group: Int = 0) raises -> Tuple[Int, Int]:
        """Return a group's half-open byte range."""
        self._check_group(group)
        return (self._starts[group], self._ends[group])

    def group(self, text: String, group: Int = 0) raises -> String:
        """Copy a captured substring from the original input."""
        self._check_group(group)
        var start = self._starts[group]
        var end = self._ends[group]
        if start < 0:
            raise Error(String(t"capture group {group} did not participate"))
        return String(text[byte=start:end])

    def group_optional(
        self, text: String, group: Int = 0
    ) raises -> Optional[String]:
        """Return a captured substring, or None for an unmatched group."""
        self._check_group(group)
        var start = self._starts[group]
        if start < 0:
            return None
        return String(text[byte = start : self._ends[group]])


def _is_byte_capture_atom[nodes: List[RegexNode], node_index: Int]() -> Bool:
    """Recognize an atom that consumes exactly one byte."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return node[LiteralNode].value.byte_length() == 1
    elif node.isa[BracketClassNode]():
        comptime bracket = node[BracketClassNode]
        comptime for item in range(bracket.count):
            comptime if bracket.highs[item] > 255:
                return False
        return True
    elif node.isa[CharClassNode]():
        comptime kind = node[CharClassNode].kind
        return kind != CHAR_UNICODE_DOT and kind != CHAR_UNICODE_DOTALL
    else:
        return False


def _capture_atom_index[nodes: List[RegexNode], capture_child: Int]() -> Int:
    comptime node = nodes[capture_child]
    comptime if node.isa[RepeatNode]():
        return node[RepeatNode].child
    return capture_child


def _capture_minimum[nodes: List[RegexNode], capture_child: Int]() -> Int:
    comptime node = nodes[capture_child]
    comptime if node.isa[RepeatNode]():
        return node[RepeatNode].minimum
    return 1


def _capture_maximum[nodes: List[RegexNode], capture_child: Int]() -> Int:
    comptime node = nodes[capture_child]
    comptime if node.isa[RepeatNode]():
        return node[RepeatNode].maximum
    return 1


@always_inline
def _byte_capture_atom_accepts[
    nodes: List[RegexNode], node_index: Int
](value: Int) -> Bool:
    """Test one byte against a compile-time-selected capture atom."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return value == Int(node[LiteralNode].value.as_bytes()[0])
    elif node.isa[BracketClassNode]():
        return _bracket_accepts[node[BracketClassNode]](value)
    else:
        return _accepts_class[node[CharClassNode].kind](value)


def _is_exact_assertion[
    nodes: List[RegexNode], node_index: Int, kind: Int
]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[ZeroWidthNode]():
        return node[ZeroWidthNode].kind == kind
    return False


def _capture_delimiter_is_disjoint[
    nodes: List[RegexNode], delimiter_index: Int, atom_index: Int
]() -> Bool:
    comptime node = nodes[delimiter_index]
    comptime if node.isa[LiteralNode]():
        comptime delimiter = node[LiteralNode]
        comptime if delimiter.value.byte_length() == 1:
            comptime value = Int(delimiter.value.as_bytes()[0])
            return not _byte_capture_atom_accepts[nodes, atom_index](value)
    return False


def _is_delimited_capture_field[
    regex: Regex, root: SequenceNode, group: Int
]() -> Bool:
    comptime node = regex.capture_nodes[root.items[2 * group - 1]]
    comptime if node.isa[CaptureNode]():
        comptime capture = node[CaptureNode]
        comptime if capture.index != group:
            return False
        comptime child = regex.capture_nodes[capture.child]
        comptime if child.isa[RepeatNode]():
            comptime if child[RepeatNode].maximum == 0:
                return False
        comptime atom_index = _capture_atom_index[
            regex.capture_nodes, capture.child
        ]()
        comptime if not _is_byte_capture_atom[
            regex.capture_nodes, atom_index
        ]():
            return False
        comptime if group < regex.capture_count:
            return _capture_delimiter_is_disjoint[
                regex.capture_nodes, root.items[2 * group], atom_index
            ]()
        return True
    return False


def _is_delimited_capture_sequence[regex: Regex, root: SequenceNode]() -> Bool:
    comptime if root.count != 2 * regex.capture_count + 1:
        return False
    comptime if not _is_exact_assertion[
        regex.capture_nodes, root.items[0], ASSERT_INPUT_START
    ]():
        return False
    comptime if not _is_exact_assertion[
        regex.capture_nodes,
        root.items[2 * regex.capture_count],
        ASSERT_INPUT_END,
    ]():
        return False
    comptime for group in range(1, regex.capture_count + 1):
        comptime if not _is_delimited_capture_field[regex, root, group]():
            return False
    return True


def _is_delimited_capture_record[regex: Regex]() -> Bool:
    """Recognize `^(field);(field);...$` without ambiguous delimiters."""
    comptime if regex.capture_count == 0:
        return False
    comptime root = regex.capture_nodes[regex.capture_root]
    comptime if root.isa[SequenceNode]():
        return _is_delimited_capture_sequence[regex, root[SequenceNode]]()
    return False


def _is_capture_group_at[
    regex: Regex, root: SequenceNode, item: Int, group: Int
]() -> Bool:
    comptime node = regex.capture_nodes[root.items[item]]
    comptime if node.isa[CaptureNode]():
        return node[CaptureNode].index == group
    return False


def _capture_sequence_stops_before_literal[
    regex: Regex, capture_index: Int, delimiter_index: Int
]() -> Bool:
    """Prove a captured sequence's final repeat excludes its delimiter."""
    comptime capture = regex.capture_nodes[capture_index][CaptureNode]
    comptime child = regex.capture_nodes[capture.child]
    comptime delimiter = regex.capture_nodes[delimiter_index]
    comptime if (
        not child.isa[SequenceNode]()
        or not delimiter.isa[LiteralNode]()
        or delimiter[LiteralNode].value.byte_length() != 1
    ):
        return False
    else:
        comptime sequence = child[SequenceNode]
        comptime if sequence.count == 0:
            return False
        else:
            comptime final = regex.capture_nodes[
                sequence.items[sequence.count - 1]
            ]
            comptime if not final.isa[RepeatNode]():
                return False
            else:
                comptime repeat = final[RepeatNode]
                comptime if not _is_byte_capture_atom[
                    regex.capture_nodes, repeat.child
                ]():
                    return False
                else:
                    comptime value = Int(
                        delimiter[LiteralNode].value.as_bytes()[0]
                    )
                    return not _byte_capture_atom_accepts[
                        regex.capture_nodes, repeat.child
                    ](value)


def _is_anchored_lazy_capture_record[regex: Regex]() -> Bool:
    """Recognize deterministic captured prefixes followed by a lazy body."""
    comptime if regex.capture_count != 5:
        return False
    else:
        comptime root_node = regex.capture_nodes[regex.capture_root]
        comptime if not root_node.isa[SequenceNode]():
            return False
        else:
            comptime root = root_node[SequenceNode]
            comptime if root.count != 13:
                return False
            elif (
                not _is_exact_assertion[
                    regex.capture_nodes, root.items[0], ASSERT_INPUT_START
                ]()
                or not _is_exact_assertion[
                    regex.capture_nodes, root.items[12], ASSERT_INPUT_END
                ]()
                or not _is_capture_group_at[regex, root, 1, 1]()
                or not _is_capture_group_at[regex, root, 3, 2]()
                or not _is_capture_group_at[regex, root, 6, 3]()
                or not _is_capture_group_at[regex, root, 7, 4]()
                or not _is_capture_group_at[regex, root, 10, 5]()
                or not regex.capture_nodes[root.items[2]].isa[LiteralNode]()
                or not regex.capture_nodes[root.items[5]].isa[LiteralNode]()
                or not regex.capture_nodes[root.items[8]].isa[LiteralNode]()
                or not regex.capture_nodes[root.items[9]].isa[LiteralNode]()
                or not regex.capture_nodes[root.items[11]].isa[LiteralNode]()
                or not _capture_sequence_stops_before_literal[
                    regex, root.items[1], root.items[2]
                ]()
            ):
                return False
            else:
                comptime level = regex.capture_nodes[root.items[3]][CaptureNode]
                comptime header = regex.capture_nodes[root.items[6]][
                    CaptureNode
                ]
                comptime body = regex.capture_nodes[root.items[7]][CaptureNode]
                comptime tail = regex.capture_nodes[root.items[10]][CaptureNode]
                comptime body_repeat = regex.capture_nodes[body.child]
                comptime tail_repeat = regex.capture_nodes[tail.child]
                comptime if (
                    not _is_byte_capture_atom[
                        regex.capture_nodes, level.child
                    ]()
                    or not _is_byte_capture_atom[
                        regex.capture_nodes, root.items[4]
                    ]()
                    or not regex.capture_nodes[header.child].isa[RepeatNode]()
                    or not body_repeat.isa[RepeatNode]()
                    or not tail_repeat.isa[RepeatNode]()
                ):
                    return False
                else:
                    comptime lazy = body_repeat[RepeatNode]
                    comptime body_atom = regex.capture_nodes[lazy.child]
                    comptime suffix = tail_repeat[RepeatNode]
                    comptime if not body_atom.isa[CharClassNode]():
                        return False
                    else:
                        return (
                            lazy.minimum == 0
                            and lazy.maximum < 0
                            and not lazy.greedy
                            and body_atom[CharClassNode].kind == CHAR_BYTE_DOT
                            and suffix.minimum == 0
                            and suffix.maximum < 0
                            and suffix.greedy
                            and _is_byte_capture_atom[
                                regex.capture_nodes, suffix.child
                            ]()
                        )


@always_inline
def _match_capture_child_or_node[
    nodes: List[RegexNode], node_index: Int
](text: ImmStringSpan, start: Int) -> Optional[_MatchResult]:
    comptime node = nodes[node_index]
    comptime if node.isa[CaptureNode]():
        return _match_node[nodes, node[CaptureNode].child](text, start)
    return _match_node[nodes, node_index](text, start)


@always_inline
def _matches_anchored_lazy_capture_record[
    regex: Regex
](text: ImmStringSpan) -> Bool:
    """Match an anchored lazy-body capture record from its terminal suffix."""
    comptime root = regex.capture_nodes[regex.capture_root][SequenceNode]
    var position = 0
    comptime for item in range(1, 7):
        var matched = _match_capture_child_or_node[
            regex.capture_nodes, root.items[item]
        ](text, position)
        if not matched:
            return False
        position += matched.unsafe_value().consumed()

    comptime prefix = regex.capture_nodes[root.items[8]][LiteralNode]
    comptime anchor = regex.capture_nodes[root.items[9]][LiteralNode]
    comptime body = regex.capture_nodes[root.items[7]][CaptureNode]
    comptime body_repeat = regex.capture_nodes[body.child][RepeatNode]
    comptime body_kind = regex.capture_nodes[body_repeat.child][
        CharClassNode
    ].kind
    var candidate = text.find(
        anchor.value, position + prefix.value.byte_length()
    )
    while candidate >= 0:
        var suffix_start = candidate - prefix.value.byte_length()
        if suffix_start >= position and _match_literal[prefix.value](
            text, suffix_start
        ):
            var body_matches = True
            for offset in range(position, suffix_start):
                if not _accepts_class[body_kind](Int(text.as_bytes()[offset])):
                    body_matches = False
                    break
            if body_matches:
                comptime tail = regex.capture_nodes[root.items[10]][CaptureNode]
                comptime closing = regex.capture_nodes[root.items[11]][
                    LiteralNode
                ]
                var tail_start = candidate + anchor.value.byte_length()
                var tail_match = _match_node[regex.capture_nodes, tail.child](
                    text, tail_start
                )
                if tail_match:
                    var closing_start = (
                        tail_start + tail_match.unsafe_value().consumed()
                    )
                    if (
                        _match_literal[closing.value](text, closing_start)
                        and closing_start + closing.value.byte_length()
                        == text.byte_length()
                    ):
                        return True
        candidate = text.find(anchor.value, candidate + 1)
    return False


@always_inline
def _find_delimited_capture_record[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[
    RegexMatch[regex.capture_count]
]:
    """Match a deterministic anchored capture record in one linear scan."""
    if search_start > 0:
        return None
    comptime root = regex.capture_nodes[regex.capture_root][SequenceNode]
    var starts = StaticTuple[Int, regex.capture_count + 1]()
    var ends = StaticTuple[Int, regex.capture_count + 1]()
    comptime for group in range(regex.capture_count + 1):
        starts[group] = -1
        ends[group] = -1

    var position = 0
    var length = text.byte_length()
    comptime for group in range(1, regex.capture_count + 1):
        comptime capture = regex.capture_nodes[root.items[2 * group - 1]][
            CaptureNode
        ]
        comptime atom_index = _capture_atom_index[
            regex.capture_nodes, capture.child
        ]()
        comptime minimum = _capture_minimum[
            regex.capture_nodes, capture.child
        ]()
        comptime maximum = _capture_maximum[
            regex.capture_nodes, capture.child
        ]()

        var field_start = position
        comptime if group < regex.capture_count:
            comptime delimiter = regex.capture_nodes[root.items[2 * group]][
                LiteralNode
            ]
            comptime delimiter_byte = Int(delimiter.value.as_bytes()[0])
            while (
                position < length
                and Int(text.as_bytes()[position]) != delimiter_byte
            ):
                if not _byte_capture_atom_accepts[
                    regex.capture_nodes, atom_index
                ](Int(text.as_bytes()[position])):
                    return None
                position += 1
            if position == length:
                return None
        else:
            while position < length:
                if not _byte_capture_atom_accepts[
                    regex.capture_nodes, atom_index
                ](Int(text.as_bytes()[position])):
                    return None
                position += 1

        var field_length = position - field_start
        if field_length < minimum:
            return None
        comptime if maximum >= 0:
            if field_length > maximum:
                return None
        starts[capture.index] = field_start
        ends[capture.index] = position
        comptime if group < regex.capture_count:
            position += 1

    starts[0] = 0
    ends[0] = length
    return RegexMatch[regex.capture_count](starts, ends)


def _capture_subtree_mask[nodes: List[RegexNode], node_index: Int]() -> Int:
    comptime node = nodes[node_index]
    comptime if node.isa[CaptureNode]():
        comptime capture = node[CaptureNode]
        return (Int(1) << (capture.index - 1)) | _capture_subtree_mask[
            nodes, capture.child
        ]()
    elif node.isa[RepeatNode]():
        return _capture_subtree_mask[nodes, node[RepeatNode].child]()
    elif node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        var mask = 0
        comptime for item in range(sequence.count):
            mask |= _capture_subtree_mask[nodes, sequence.items[item]]()
        return mask
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        var mask = 0
        comptime for option in range(alternation.count):
            mask |= _capture_subtree_mask[nodes, alternation.options[option]]()
        return mask
    return 0


def _fixed_capture_sequence_item_mask[
    regex: Regex, sequence: SequenceNode, item: Int
]() -> Int:
    """Return a handled item's capture mask, or `-1` when ambiguous."""
    comptime node = regex.capture_nodes[sequence.items[item]]
    comptime if node.isa[CaptureNode]():
        comptime capture = node[CaptureNode]
        comptime if (
            _fixed_node_width[regex.capture_nodes, capture.child]() > 0
            and _capture_subtree_mask[regex.capture_nodes, capture.child]() == 0
        ):
            return Int(1) << (capture.index - 1)
        return -1
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime child = regex.capture_nodes[repeat.child]
        comptime if (
            item + 1 == sequence.count
            and repeat.minimum == 0
            and repeat.maximum == 1
            and child.isa[CaptureNode]()
        ):
            comptime capture = child[CaptureNode]
            comptime if (
                _fixed_node_width[regex.capture_nodes, capture.child]() > 0
                and _capture_subtree_mask[regex.capture_nodes, capture.child]()
                == 0
            ):
                return Int(1) << (capture.index - 1)
        return -1
    else:
        comptime if (
            _capture_subtree_mask[regex.capture_nodes, sequence.items[item]]()
            == 0
            and _fixed_node_width[regex.capture_nodes, sequence.items[item]]()
            >= 0
        ):
            return 0
        return -1


def _is_fixed_capture_sequence[regex: Regex]() -> Bool:
    """Recognize fixed items followed by at most one optional capture."""
    comptime if regex.capture_count == 0:
        return False
    comptime root_node = regex.capture_nodes[regex.capture_root]
    comptime if root_node.isa[SequenceNode]():
        comptime root = root_node[SequenceNode]
        var mask = 0
        comptime for item in range(root.count):
            comptime item_mask = _fixed_capture_sequence_item_mask[
                regex, root, item
            ]()
            comptime if item_mask < 0:
                return False
            mask |= item_mask
        return mask == (Int(1) << regex.capture_count) - 1
    return False


@always_inline
def _fixed_capture_sequence_match_at[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Optional[RegexMatch[regex.capture_count]]:
    comptime sequence = regex.capture_nodes[regex.capture_root][SequenceNode]
    var starts = StaticTuple[Int, regex.capture_count + 1]()
    var ends = StaticTuple[Int, regex.capture_count + 1]()
    comptime for group in range(regex.capture_count + 1):
        starts[group] = -1
        ends[group] = -1
    var position = start
    comptime for item in range(sequence.count):
        comptime node = regex.capture_nodes[sequence.items[item]]
        comptime if node.isa[CaptureNode]():
            comptime capture = node[CaptureNode]
            var matched = _match_node[regex.capture_nodes, capture.child](
                text, position
            )
            if not matched:
                return None
            starts[capture.index] = position
            position += matched.unsafe_value().consumed()
            ends[capture.index] = position
        elif node.isa[RepeatNode]():
            comptime capture = regex.capture_nodes[node[RepeatNode].child][
                CaptureNode
            ]
            var matched = _match_node[regex.capture_nodes, capture.child](
                text, position
            )
            if matched:
                starts[capture.index] = position
                position += matched.unsafe_value().consumed()
                ends[capture.index] = position
        else:
            var matched = _match_node[
                regex.capture_nodes, sequence.items[item]
            ](text, position)
            if not matched:
                return None
            position += matched.unsafe_value().consumed()
    starts[0] = start
    ends[0] = position
    return RegexMatch[regex.capture_count](starts, ends)


@always_inline
def _find_fixed_capture_sequence[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[
    RegexMatch[regex.capture_count]
]:
    var start = search_start
    while start <= text.byte_length():
        var found = _fixed_capture_sequence_match_at[regex](text, start)
        if found:
            return found^
        start += 1
    return None


def _capture_stops_before_delimiter[
    regex: Regex,
    capture_index: Int,
    group: Int,
    delimiter_index: Int,
]() -> Bool:
    comptime node = regex.capture_nodes[capture_index]
    comptime if node.isa[CaptureNode]():
        comptime capture = node[CaptureNode]
        comptime if (
            capture.index != group
            or _capture_subtree_mask[regex.capture_nodes, capture.child]() != 0
        ):
            return False
        comptime if _fixed_node_width[regex.capture_nodes, capture.child]() > 0:
            return True
        comptime child = regex.capture_nodes[capture.child]
        comptime if child.isa[RepeatNode]():
            comptime repeat = child[RepeatNode]
            comptime if repeat.maximum != 0 and _is_byte_capture_atom[
                regex.capture_nodes, repeat.child
            ]():
                return _capture_delimiter_is_disjoint[
                    regex.capture_nodes, delimiter_index, repeat.child
                ]()
    return False


def _is_optional_delimited_capture_tail[
    regex: Regex, node_index: Int, group: Int
]() -> Bool:
    comptime node = regex.capture_nodes[node_index]
    comptime if node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime child = regex.capture_nodes[repeat.child]
        comptime if (
            repeat.minimum == 0
            and repeat.maximum == 1
            and child.isa[SequenceNode]()
        ):
            comptime sequence = child[SequenceNode]
            comptime if sequence.count == 2:
                comptime delimiter = regex.capture_nodes[sequence.items[0]]
                comptime capture_node = regex.capture_nodes[sequence.items[1]]
                comptime if delimiter.isa[LiteralNode]() and capture_node.isa[
                    CaptureNode
                ]():
                    comptime capture = capture_node[CaptureNode]
                    comptime if (
                        delimiter[LiteralNode].value.byte_length() == 1
                        and capture.index == group
                        and _capture_subtree_mask[
                            regex.capture_nodes, capture.child
                        ]()
                        == 0
                    ):
                        comptime if _fixed_node_width[
                            regex.capture_nodes, capture.child
                        ]() > 0:
                            return True
                        comptime captured = regex.capture_nodes[capture.child]
                        comptime if captured.isa[RepeatNode]():
                            return (
                                captured[RepeatNode].maximum != 0
                                and _is_byte_capture_atom[
                                    regex.capture_nodes,
                                    captured[RepeatNode].child,
                                ]()
                            )
    return False


def _is_delimited_capture_record_with_optional_tail[regex: Regex]() -> Bool:
    """Recognize anchored records whose final delimited field is optional."""
    comptime if regex.capture_count < 2:
        return False
    comptime root_node = regex.capture_nodes[regex.capture_root]
    comptime if root_node.isa[SequenceNode]():
        comptime root = root_node[SequenceNode]
        comptime if root.count != 2 * regex.capture_count:
            return False
        comptime if not _is_exact_assertion[
            regex.capture_nodes, root.items[0], ASSERT_INPUT_START
        ]() or not _is_exact_assertion[
            regex.capture_nodes,
            root.items[root.count - 1],
            ASSERT_INPUT_END,
        ]():
            return False
        comptime for group in range(1, regex.capture_count - 1):
            comptime if not _capture_stops_before_delimiter[
                regex,
                root.items[2 * group - 1],
                group,
                root.items[2 * group],
            ]():
                return False
        comptime tail_index = root.items[root.count - 2]
        comptime if _is_optional_delimited_capture_tail[
            regex, tail_index, regex.capture_count
        ]():
            comptime tail = regex.capture_nodes[tail_index][RepeatNode]
            comptime tail_sequence = regex.capture_nodes[tail.child][
                SequenceNode
            ]
            return _capture_stops_before_delimiter[
                regex,
                root.items[root.count - 3],
                regex.capture_count - 1,
                tail_sequence.items[0],
            ]()
        return False
    return False


@always_inline
def _find_delimited_capture_record_with_optional_tail[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[
    RegexMatch[regex.capture_count]
]:
    if search_start > 0:
        return None
    comptime root = regex.capture_nodes[regex.capture_root][SequenceNode]
    comptime tail = regex.capture_nodes[root.items[root.count - 2]][RepeatNode]
    comptime tail_sequence = regex.capture_nodes[tail.child][SequenceNode]
    comptime tail_delimiter = regex.capture_nodes[tail_sequence.items[0]][
        LiteralNode
    ]
    comptime tail_capture = regex.capture_nodes[tail_sequence.items[1]][
        CaptureNode
    ]
    var starts = StaticTuple[Int, regex.capture_count + 1]()
    var ends = StaticTuple[Int, regex.capture_count + 1]()
    comptime for group in range(regex.capture_count + 1):
        starts[group] = -1
        ends[group] = -1
    var position = 0

    comptime for group in range(1, regex.capture_count):
        comptime capture = regex.capture_nodes[root.items[2 * group - 1]][
            CaptureNode
        ]
        var matched = _match_node[regex.capture_nodes, capture.child](
            text, position
        )
        if not matched:
            return None
        starts[capture.index] = position
        position += matched.unsafe_value().consumed()
        ends[capture.index] = position
        comptime if group < regex.capture_count - 1:
            comptime delimiter = regex.capture_nodes[root.items[2 * group]][
                LiteralNode
            ]
            if not _match_literal[delimiter.value](text, position):
                return None
            position += delimiter.value.byte_length()

    if position < text.byte_length():
        if not _match_literal[tail_delimiter.value](text, position):
            return None
        position += tail_delimiter.value.byte_length()
        var matched = _match_node[regex.capture_nodes, tail_capture.child](
            text, position
        )
        if not matched:
            return None
        starts[tail_capture.index] = position
        position += matched.unsafe_value().consumed()
        ends[tail_capture.index] = position
    if position != text.byte_length():
        return None
    starts[0] = 0
    ends[0] = position
    return RegexMatch[regex.capture_count](starts, ends)


def _is_captured_fixed_width_alternation_node[
    regex: Regex, node_index: Int
]() -> Bool:
    comptime node = regex.capture_nodes[node_index]
    comptime if node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count < 2:
            return False
        comptime for option in range(alternation.count):
            comptime option_node = regex.capture_nodes[
                alternation.options[option]
            ]
            comptime if not option_node.isa[CaptureNode]():
                return False
            comptime capture = option_node[CaptureNode]
            comptime if (
                _fixed_node_width[regex.capture_nodes, capture.child]() <= 0
                or _capture_subtree_mask[regex.capture_nodes, capture.child]()
                != 0
            ):
                return False
        return True
    return False


def _captured_fixed_width_alternation_index[regex: Regex]() -> Int:
    """Find a root or assertion-wrapped captured fixed-width alternation."""
    comptime root = regex.capture_nodes[regex.capture_root]
    comptime if _is_captured_fixed_width_alternation_node[
        regex, regex.capture_root
    ]():
        return regex.capture_root
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if (
            sequence.count == 3
            and regex.capture_nodes[sequence.items[0]].isa[ZeroWidthNode]()
            and regex.capture_nodes[sequence.items[2]].isa[ZeroWidthNode]()
            and _is_captured_fixed_width_alternation_node[
                regex, sequence.items[1]
            ]()
        ):
            return sequence.items[1]
    return -1


@always_inline
def _find_captured_fixed_width_alternation[
    regex: Regex, alternation_index: Int
](text: ImmStringSpan, search_start: Int) -> Optional[
    RegexMatch[regex.capture_count]
]:
    comptime alternation = regex.capture_nodes[alternation_index][OrNode]
    comptime wrapped = alternation_index != regex.capture_root
    var start = search_start
    while start < text.byte_length():
        comptime if wrapped:
            comptime root = regex.capture_nodes[regex.capture_root][
                SequenceNode
            ]
            var prefix = _match_node[regex.capture_nodes, root.items[0]](
                text, start
            )
            if not prefix:
                start += 1
                continue
        comptime for option in range(alternation.count):
            comptime capture = regex.capture_nodes[alternation.options[option]][
                CaptureNode
            ]
            var matched = _match_node[regex.capture_nodes, capture.child](
                text, start
            )
            if not matched:
                continue
            var end = start + matched.unsafe_value().consumed()
            comptime if wrapped:
                comptime root = regex.capture_nodes[regex.capture_root][
                    SequenceNode
                ]
                var suffix = _match_node[regex.capture_nodes, root.items[2]](
                    text, end
                )
                if not suffix:
                    continue
            var starts = StaticTuple[Int, regex.capture_count + 1]()
            var ends = StaticTuple[Int, regex.capture_count + 1]()
            comptime for group in range(regex.capture_count + 1):
                starts[group] = -1
                ends[group] = -1
            starts[0] = start
            ends[0] = end
            starts[capture.index] = start
            ends[capture.index] = end
            return RegexMatch[regex.capture_count](starts, ends)
        start += 1
    return None


def _is_literal_capture_run_alternation[regex: Regex]() -> Bool:
    """Recognize `literal(class+)|...` in the capture-preserving AST."""
    comptime root = regex.capture_nodes[regex.capture_root]
    comptime if root.isa[OrNode]():
        comptime alternation = root[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for option in range(alternation.count):
            comptime node = regex.capture_nodes[alternation.options[option]]
            comptime if node.isa[SequenceNode]():
                comptime sequence = node[SequenceNode]
                comptime if sequence.count != 2:
                    return False
                comptime literal = regex.capture_nodes[sequence.items[0]]
                comptime capture = regex.capture_nodes[sequence.items[1]]
                comptime if literal.isa[LiteralNode]() and capture.isa[
                    CaptureNode
                ]():
                    comptime if literal[LiteralNode].value.byte_length() == 0:
                        return False
                    comptime repeat_node = regex.capture_nodes[
                        capture[CaptureNode].child
                    ]
                    comptime if repeat_node.isa[RepeatNode]():
                        comptime repeat = repeat_node[RepeatNode]
                        comptime if repeat.minimum <= 0:
                            return False
                        comptime child = regex.capture_nodes[repeat.child]
                        comptime if not child.isa[
                            CharClassNode
                        ]() and not child.isa[BracketClassNode]():
                            return False
                    else:
                        return False
                else:
                    return False
            else:
                return False
        return True
    return False


def _is_captured_literal_run_alternation[regex: Regex]() -> Bool:
    """Recognize `(literal+)|(literal+)|...` capture alternatives."""
    comptime root = regex.capture_nodes[regex.capture_root]
    comptime if root.isa[OrNode]():
        comptime alternation = root[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for option in range(alternation.count):
            comptime node = regex.capture_nodes[alternation.options[option]]
            comptime if node.isa[CaptureNode]():
                comptime capture = node[CaptureNode]
                comptime repeated = regex.capture_nodes[capture.child]
                comptime if repeated.isa[RepeatNode]():
                    comptime repeat = repeated[RepeatNode]
                    comptime if repeat.minimum <= 0:
                        return False
                    comptime child = regex.capture_nodes[repeat.child]
                    comptime if child.isa[LiteralNode]():
                        comptime if child[LiteralNode].value.byte_length() != 1:
                            return False
                    else:
                        return False
                else:
                    return False
            else:
                return False
        return True
    return False


def _captured_literal_run_group_map[regex: Regex]() -> StaticTuple[Int, 256]:
    """Map each byte to its first matching capture-alternative group."""
    var groups = StaticTuple[Int, 256]()
    comptime root = regex.capture_nodes[regex.capture_root][OrNode]
    comptime for option in range(root.count):
        comptime capture = regex.capture_nodes[root.options[option]][
            CaptureNode
        ]
        comptime repeat = regex.capture_nodes[capture.child][RepeatNode]
        comptime literal = regex.capture_nodes[repeat.child][LiteralNode]
        comptime value = Int(literal.value.as_bytes()[0])
        if groups[value] == 0:
            groups[value] = capture.index
    return groups


@always_inline
def _find_captured_literal_run_alternation[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Optional[RegexMatch[regex.capture_count]]:
    """Execute a normalized byte-class run while retaining capture identity."""
    comptime groups = _captured_literal_run_group_map[regex]()
    comptime root = regex.capture_nodes[regex.capture_root][OrNode]
    var position = start
    while position < text.byte_length():
        var group = groups[Int(text.as_bytes()[position])]
        if group == 0:
            position += 1
            continue

        comptime for option in range(root.count):
            comptime capture = regex.capture_nodes[root.options[option]][
                CaptureNode
            ]
            if group != capture.index:
                continue
            comptime repeat = regex.capture_nodes[capture.child][RepeatNode]
            var end = position
            var repetitions = 0
            while (
                end < text.byte_length()
                and groups[Int(text.as_bytes()[end])] == group
            ):
                comptime if repeat.maximum >= 0:
                    if repetitions >= repeat.maximum:
                        break
                end += 1
                repetitions += 1
                comptime if not repeat.greedy:
                    if repetitions >= repeat.minimum:
                        break
            if repetitions >= repeat.minimum:
                var starts = StaticTuple[Int, regex.capture_count + 1]()
                var ends = StaticTuple[Int, regex.capture_count + 1]()
                comptime for capture_group in range(regex.capture_count + 1):
                    starts[capture_group] = -1
                    ends[capture_group] = -1
                starts[0] = position
                ends[0] = end
                starts[group] = position
                ends[group] = end
                return RegexMatch[regex.capture_count](starts, ends)
        position += 1
    return None


@always_inline
def _literal_capture_run_match_at[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Optional[RegexMatch[regex.capture_count]]:
    """Try every branch of a normalized capture plan at one byte offset."""
    comptime root = regex.capture_nodes[regex.capture_root][OrNode]
    comptime for option in range(root.count):
        comptime sequence = regex.capture_nodes[root.options[option]][
            SequenceNode
        ]
        comptime literal = regex.capture_nodes[sequence.items[0]][LiteralNode]
        if not _match_literal[literal.value](text, start):
            continue
        comptime capture = regex.capture_nodes[sequence.items[1]][CaptureNode]
        comptime repeat = regex.capture_nodes[capture.child][RepeatNode]
        var capture_start = start + literal.value.byte_length()
        var capture_end = capture_start
        var repetitions = 0
        while True:
            comptime if repeat.maximum >= 0:
                if repetitions >= repeat.maximum:
                    break
            var matched = _match_node[regex.capture_nodes, repeat.child](
                text, capture_end
            )
            if not matched:
                break
            var consumed = matched.unsafe_value().consumed()
            if consumed == 0:
                break
            capture_end += consumed
            repetitions += 1
            comptime if not repeat.greedy:
                if repetitions >= repeat.minimum:
                    break
        if repetitions >= repeat.minimum:
            var starts = StaticTuple[Int, regex.capture_count + 1]()
            var ends = StaticTuple[Int, regex.capture_count + 1]()
            comptime for group in range(regex.capture_count + 1):
                starts[group] = -1
                ends[group] = -1
            starts[0] = start
            ends[0] = capture_end
            starts[capture.index] = capture_start
            ends[capture.index] = capture_end
            return RegexMatch[regex.capture_count](starts, ends)
    return None


def _literal_capture_prefix_max_width[regex: Regex]() -> Int:
    comptime root = regex.capture_nodes[regex.capture_root][OrNode]
    var maximum = 0
    comptime for option in range(root.count):
        comptime sequence = regex.capture_nodes[root.options[option]][
            SequenceNode
        ]
        comptime literal = regex.capture_nodes[sequence.items[0]][LiteralNode]
        maximum = max(maximum, literal.value.byte_length())
    return maximum


@always_inline
def _find_literal_capture_run_alternation[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Optional[RegexMatch[regex.capture_count]]:
    """Execute a normalized literal-prefix/captured-run alternation plan."""
    comptime root = regex.capture_nodes[regex.capture_root][OrNode]
    comptime maximum = _literal_capture_prefix_max_width[regex]()
    var length = text.byte_length()
    var offset = start
    var pointer = text.unsafe_ptr()
    while offset + CLASS_SIMD_WIDTH + maximum - 1 <= length:
        var first_values = pointer.unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](offset)
        var candidates = SIMD[.bool, CLASS_SIMD_WIDTH](fill=False)
        comptime for option in range(root.count):
            comptime sequence = regex.capture_nodes[root.options[option]][
                SequenceNode
            ]
            comptime literal = regex.capture_nodes[sequence.items[0]][
                LiteralNode
            ]
            var branch = first_values.eq(literal.value.as_bytes()[0])
            comptime for position in range(1, literal.value.byte_length()):
                var values = pointer.unsafe_load[
                    width=CLASS_SIMD_WIDTH, alignment=1
                ](offset + position)
                branch &= values.eq(literal.value.as_bytes()[position])
            candidates |= branch
        var pending = pack_bits(candidates)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            var found = _literal_capture_run_match_at[regex](
                text, offset + lane
            )
            if found:
                return found^
        offset += CLASS_SIMD_WIDTH

    while offset < length:
        var found = _literal_capture_run_match_at[regex](text, offset)
        if found:
            return found^
        offset += 1
    return None


def _leading_literal_index[nodes: List[RegexNode], node_index: Int]() -> Int:
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return node_index
    elif node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime for i in range(sequence.count):
            comptime item = nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]() or item.isa[ZeroWidthNode]():
                pass
            elif item.isa[LiteralNode]():
                return sequence.items[i]
            else:
                return -1
    return -1


def _alternation_leading_prefix_length[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    comptime if alternation.count == 0:
        return 0
    comptime first_index = _leading_literal_index[
        nodes, alternation.options[0]
    ]()
    comptime if first_index < 0:
        return 0
    comptime first = nodes[first_index][LiteralNode]
    var length = first.value.byte_length()
    comptime for option in range(1, alternation.count):
        comptime literal_index = _leading_literal_index[
            nodes, alternation.options[option]
        ]()
        comptime if literal_index < 0:
            return 0
        comptime literal = nodes[literal_index][LiteralNode]
        length = min(length, literal.value.byte_length())
        var shared = 0
        while shared < length and (
            first.value.as_bytes()[shared] == literal.value.as_bytes()[shared]
        ):
            shared += 1
        length = shared
    return length


def _has_leading_literal_prefilter[regex: Regex]() -> Bool:
    """Return whether `_prefilter_start` finds an exact match start."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        return True
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime for i in range(sequence.count):
            comptime item = regex.nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]() or item.isa[ZeroWidthNode]():
                continue
            return item.isa[LiteralNode]()
        return False
    comptime if root.isa[OrNode]():
        return (
            _alternation_leading_prefix_length[regex.nodes, root[OrNode]]() > 0
        )
    return False


@always_inline
def _prefilter_start[regex: Regex](text: ImmStringSpan, start: Int) -> Int:
    """Skip directly to a required literal at the match's leading edge."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        return text.find(root[LiteralNode].value, start)
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime for i in range(sequence.count):
            comptime item = regex.nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]() or item.isa[ZeroWidthNode]():
                continue
            comptime if item.isa[LiteralNode]():
                return text.find(item[LiteralNode].value, start)
            return start
    comptime if root.isa[OrNode]():
        comptime alternation = root[OrNode]
        comptime prefix_length = _alternation_leading_prefix_length[
            regex.nodes, alternation
        ]()
        comptime if prefix_length > 0:
            comptime literal_index = _leading_literal_index[
                regex.nodes, alternation.options[0]
            ]()
            comptime literal = regex.nodes[literal_index][LiteralNode]
            return text.find(literal.value[byte=0:prefix_length], start)
    return start


@always_inline
def find_span[
    regex: Regex
](text: ImmStringSpan, start: Int = 0) -> Optional[
    RegexMatch[regex.capture_count]
]:
    """Find the next leftmost-first match at or after a byte offset."""
    var search_start = max(0, start)
    if search_start > text.byte_length():
        return None
    comptime if regex.capture_count > 0:
        comptime if _is_delimited_capture_record[regex]():
            return _find_delimited_capture_record[regex](text, search_start)
        comptime if _is_fixed_capture_sequence[regex]():
            return _find_fixed_capture_sequence[regex](text, search_start)
        comptime if _is_delimited_capture_record_with_optional_tail[regex]():
            return _find_delimited_capture_record_with_optional_tail[regex](
                text, search_start
            )
        comptime captured_fixed_alternation = (
            _captured_fixed_width_alternation_index[regex]()
        )
        comptime if captured_fixed_alternation >= 0:
            return _find_captured_fixed_width_alternation[
                regex, captured_fixed_alternation
            ](text, search_start)
        comptime if _is_captured_literal_run_alternation[regex]():
            return _find_captured_literal_run_alternation[regex](
                text, search_start
            )
        comptime if _is_literal_capture_run_alternation[regex]():
            return _find_literal_capture_run_alternation[regex](
                text, search_start
            )
    search_start = _prefilter_start[regex](text, search_start)
    if search_start < 0:
        return None
    comptime if regex.capture_count > 0:
        comptime if _has_leading_literal_prefilter[regex]():
            while search_start >= 0:
                var captured = _nfa_match_captures_at[regex](text, search_start)
                if captured:
                    var result = captured.unsafe_value()
                    return RegexMatch[regex.capture_count](
                        result.starts, result.ends
                    )
                search_start = _prefilter_start[regex](text, search_start + 1)
            return None
        var captured = _nfa_find_captures[regex](text, search_start)
        if not captured:
            return None
        var result = captured.unsafe_value()
        return RegexMatch[regex.capture_count](result.starts, result.ends)
    else:
        var found = _nfa_find_from[regex](text, search_start)
        if not found:
            return None
        var result = found.unsafe_value()
        var starts = StaticTuple[Int, regex.capture_count + 1]()
        var ends = StaticTuple[Int, regex.capture_count + 1]()
        starts[0] = result.start
        ends[0] = result.start + result.consumed
        return RegexMatch[regex.capture_count](starts, ends)


@always_inline
def find[
    regex: Regex
](text: String, start: Int = 0) -> Optional[RegexMatch[regex.capture_count]]:
    """Owned-string convenience wrapper for `find_span`."""
    return find_span[regex](text[byte = 0 : text.byte_length()], start)


def finditer_span[
    regex: Regex
](text: ImmStringSpan) -> List[RegexMatch[regex.capture_count]]:
    """Collect leftmost, non-overlapping matches over a borrowed input."""
    var matches = List[RegexMatch[regex.capture_count]]()
    var search_start = 0
    while search_start <= text.byte_length():
        var next = find_span[regex](text, search_start)
        if not next:
            break
        var found = next.unsafe_value()
        matches.append(found)
        var end = found._ends[0]
        if end > found._starts[0]:
            search_start = end
        else:
            search_start = end + 1
    return matches^


def finditer[
    regex: Regex
](text: String) -> List[RegexMatch[regex.capture_count]]:
    """Collect leftmost, non-overlapping matches over an owned string."""
    return finditer_span[regex](text[byte = 0 : text.byte_length()])
