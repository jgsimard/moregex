"""Shared regex execution primitives and SIMD constants."""

from ._ast import (
    ASSERT_INPUT_END,
    ASSERT_INPUT_START,
    ASSERT_LINE_END,
    ASSERT_LINE_START,
    ASSERT_NON_WORD_BOUNDARY,
    ASSERT_WORD_BOUNDARY,
    CHAR_ASCII_DIGIT,
    CHAR_ASCII_NON_DIGIT,
    CHAR_ASCII_NON_WHITESPACE,
    CHAR_ASCII_NON_WORD,
    CHAR_ASCII_WHITESPACE,
    CHAR_ASCII_WORD,
    CHAR_BYTE_DOT,
    CHAR_BYTE_DOTALL,
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
    BracketClassNode,
    LiteralNode,
)
from ._syntax import Regex
from std.memory import MaybeUninit
from std.sys import simd_width_of, size_of
from std.utils import StaticTuple
from std.utils._nicheable import UnsafeSingleNicheable

comptime CLASS_SIMD_WIDTH = simd_width_of[DType.uint8]()
comptime CLASS_TAIL_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 2)
comptime CLASS_QUARTER_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 4)
comptime CLASS_EIGHTH_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 8)
comptime CLASS_SIXTEENTH_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 16)


@always_inline
def _runtime_bracket_accepts(node: BracketClassNode, value: Int) -> Bool:
    for item in range(node.count):
        if node.lows[item] <= value <= node.highs[item]:
            return not node.negated
    return node.negated


@always_inline
def _bracket_accepts[node: BracketClassNode](value: Int) -> Bool:
    comptime for item in range(node.count):
        if node.lows[item] <= value <= node.highs[item]:
            return not node.negated
    return node.negated


def _static_source_is_root_literal[regex: Regex]() -> Bool:
    """Return whether the original borrowed pattern is the root literal."""
    comptime if not regex.has_static_source:
        return False
    comptime root = regex.nodes[regex.root]
    comptime if not root.isa[LiteralNode]():
        return False
    comptime literal = root[LiteralNode]
    comptime if regex.source.byte_length() != literal.value.byte_length():
        return False
    comptime for i in range(literal.value.byte_length()):
        comptime if regex.source.as_bytes()[i] != literal.value.as_bytes()[i]:
            return False
    return True


@always_inline
def _build_bracket_masks(node: BracketClassNode) -> StaticTuple[UInt64, 4]:
    """Compile a bracket class into a 256-bit byte lookup table."""
    var masks = StaticTuple[UInt64, 4]()
    for value in range(256):
        if _runtime_bracket_accepts(node, value):
            masks[value // 64] |= UInt64(1) << UInt64(value % 64)
    return masks


struct _MatchResult(Copyable, UnsafeSingleNicheable):
    """The consumed length of a successful match.

    Zero is reserved as the invalid niche, so the stored value is one greater
    than the consumed length. This preserves zero-width matches while making
    `Optional[_MatchResult]` exactly one machine word.
    """

    var _encoded_length: Int

    @always_inline
    def __init__(out self, consumed: Int):
        comptime assert size_of[Optional[Self]]() == size_of[Int]()
        self._encoded_length = consumed + 1

    @always_inline
    def consumed(self) -> Int:
        return self._encoded_length - 1

    @staticmethod
    @always_inline
    def write_niche(memory: MutPointer[MaybeUninit[Self], _]):
        memory.unsafe_bitcast[Int]().unsafe_store(0)

    @staticmethod
    @always_inline
    def isa_niche(memory: ImmPointer[MaybeUninit[Self], _]) -> Bool:
        return memory.unsafe_bitcast[Int]()[] == 0


@fieldwise_init
struct _MatchSpanResult(Copyable):
    var matched: Bool
    var start: Int
    var end: Int


@always_inline
def _match_literal[
    value: String
](text: ImmStringSpan, start: Int) -> Optional[_MatchResult]:
    if start + value.byte_length() > text.byte_length():
        return None
    var text_bytes = text.as_bytes()
    comptime for i in range(value.byte_length()):
        comptime expected = value.as_bytes()[i]
        if text_bytes[start + i] != expected:
            return None
    return _MatchResult(value.byte_length())


@always_inline
def _is_ascii_digit(value: Int) -> Bool:
    return ord("0") <= value <= ord("9")


@always_inline
def _is_ascii_word(value: Int) -> Bool:
    var folded = value | 0x20
    return (
        (ord("a") <= folded <= ord("z"))
        or _is_ascii_digit(value)
        or value == ord("_")
    )


@always_inline
def _zero_width_matches(kind: Int, text: ImmStringSpan, position: Int) -> Bool:
    """Evaluate a standard zero-width assertion at an input position."""
    if kind == ASSERT_INPUT_START:
        return position == 0
    if kind == ASSERT_INPUT_END:
        return position == text.byte_length() or (
            position + 1 == text.byte_length()
            and Int(text.as_bytes()[position]) == ord("\n")
        )
    if kind == ASSERT_LINE_START:
        return position == 0 or Int(text.as_bytes()[position - 1]) == ord("\n")
    if kind == ASSERT_LINE_END:
        return position == text.byte_length() or Int(
            text.as_bytes()[position]
        ) == ord("\n")
    var left_is_word = position > 0 and _is_ascii_word(
        Int(text.as_bytes()[position - 1])
    )
    var right_is_word = position < text.byte_length() and _is_ascii_word(
        Int(text.as_bytes()[position])
    )
    var boundary = left_is_word != right_is_word
    return boundary if kind == ASSERT_WORD_BOUNDARY else not boundary


@always_inline
def _runtime_class_accepts(kind: Int, value: Int) -> Bool:
    """Evaluate a byte-oriented character class selected at runtime."""
    if kind == CHAR_BYTE_DOT:
        return value != ord("\n")
    if kind == CHAR_ASCII_WORD:
        return _is_ascii_word(value)
    if kind == CHAR_ASCII_DIGIT:
        return _is_ascii_digit(value)
    if kind == CHAR_ASCII_WHITESPACE:
        return value == 32 or value == 9 or value == 10 or value == 13
    if kind == CHAR_ASCII_NON_WORD:
        return not _is_ascii_word(value)
    if kind == CHAR_ASCII_NON_DIGIT:
        return not _is_ascii_digit(value)
    if kind == CHAR_ASCII_NON_WHITESPACE:
        return not (value == 32 or value == 9 or value == 10 or value == 13)
    return kind == CHAR_BYTE_DOTALL


@always_inline
def _accepts_class[kind: Int](value: Int) -> Bool:
    """Evaluate a compile-time-selected byte-oriented character class."""
    comptime if kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL:
        # Unicode classes validate code-point boundaries in `_match_class`;
        # byte-level filtering must conservatively keep every candidate.
        return True
    return _runtime_class_accepts(kind, value)


@always_inline
def _utf8_codepoint_width(text: ImmStringSpan, start: Int) -> Int:
    """Return the UTF-8 code-point width at a leading byte, or zero."""
    if start >= text.byte_length():
        return 0
    var first = Int(text.as_bytes()[start])
    if first < 0x80:
        return 1
    if first < 0xC2:
        # Continuation bytes and overlong two-byte prefixes are not starts.
        return 0
    if first < 0xE0:
        return 2 if start + 2 <= text.byte_length() else 0
    if first < 0xF0:
        return 3 if start + 3 <= text.byte_length() else 0
    if first < 0xF5:
        return 4 if start + 4 <= text.byte_length() else 0
    return 0


@always_inline
def _match_class[
    kind: Int
](text: ImmStringSpan, start: Int) -> Optional[_MatchResult]:
    if start >= text.byte_length():
        return None
    comptime if kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL:
        var width = _utf8_codepoint_width(text, start)
        if width == 0:
            return None
        comptime if kind == CHAR_UNICODE_DOT:
            if Int(text.as_bytes()[start]) == ord("\n"):
                return None
        return _MatchResult(width)
    if _accepts_class[kind](Int(text.as_bytes()[start])):
        return _MatchResult(1)
    return None


@always_inline
def _byte_range_mask[
    low: Int, high: Int, width: Int
](values: SIMD[.uint8, width]) -> SIMD[.bool, width]:
    return values.ge(SIMD[.uint8, width](UInt8(low))) & values.le(
        SIMD[.uint8, width](UInt8(high))
    )


@always_inline
def _class_mask[
    kind: Int, width: Int
](values: SIMD[.uint8, width]) -> SIMD[.bool, width]:
    comptime if kind == CHAR_BYTE_DOT:
        return values.eq(SIMD[.uint8, width](UInt8(ord("\n")))) ^ SIMD[
            .bool, width
        ](fill=True)
    elif kind == CHAR_ASCII_WORD:
        var folded = values | SIMD[.uint8, width](0x20)
        var letter = _byte_range_mask[ord("a"), ord("z"), width](folded)
        var digit = _byte_range_mask[ord("0"), ord("9"), width](values)
        return letter | digit | values.eq(SIMD[.uint8, width](UInt8(ord("_"))))
    elif kind == CHAR_ASCII_DIGIT:
        return _byte_range_mask[ord("0"), ord("9"), width](values)
    elif kind == CHAR_ASCII_WHITESPACE:
        return (
            values.eq(SIMD[.uint8, width](UInt8(32)))
            | values.eq(SIMD[.uint8, width](UInt8(9)))
            | values.eq(SIMD[.uint8, width](UInt8(10)))
            | values.eq(SIMD[.uint8, width](UInt8(13)))
        )
    elif kind == CHAR_ASCII_NON_WORD:
        return _class_mask[CHAR_ASCII_WORD, width](values) ^ SIMD[.bool, width](
            fill=True
        )
    elif kind == CHAR_ASCII_NON_DIGIT:
        return _class_mask[CHAR_ASCII_DIGIT, width](values) ^ SIMD[
            .bool, width
        ](fill=True)
    elif kind == CHAR_ASCII_NON_WHITESPACE:
        return _class_mask[CHAR_ASCII_WHITESPACE, width](values) ^ SIMD[
            .bool, width
        ](fill=True)
    else:
        return SIMD[.bool, width](fill=True)


@always_inline
def _matches_class_run[kind: Int](text: ImmStringSpan) -> Bool:
    var length = text.byte_length()
    if length == 0:
        return False
    var pointer = text.unsafe_ptr()
    var offset = 0
    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while offset + width <= length:
            # The loop guard proves the unaligned vector load is in bounds.
            var values = pointer.unsafe_load[width=width, alignment=1](offset)
            if not all(_class_mask[kind, width](values)):
                return False
            offset += width

    var bytes = text.as_bytes()
    while offset < length:
        if not _accepts_class[kind](Int(bytes[offset])):
            return False
        offset += 1
    return True


@always_inline
def _match_checksum[sum_spans: Bool](consumed: Int) -> Int:
    comptime if sum_spans:
        return consumed
    return 1


@always_inline
def _search_simd_width_ladder(
    candidate_count: Int,
    base: Int,
    scanner: Some[def[width: Int](start: Int, end: Int) -> Bool],
) -> Bool:
    """Search candidates with native-to-sixteenth-width SIMD blocks."""
    var scanned = 0
    comptime widths = [
        CLASS_SIMD_WIDTH,
        CLASS_TAIL_SIMD_WIDTH,
        CLASS_QUARTER_SIMD_WIDTH,
        CLASS_EIGHTH_SIMD_WIDTH,
        CLASS_SIXTEENTH_SIMD_WIDTH,
    ]
    comptime for width in widths:
        if candidate_count >= width:
            while scanned + width <= candidate_count:
                if scanner[width](base + scanned, 0):
                    return True
                scanned += width
            if scanned < candidate_count:
                if candidate_count - scanned >= CLASS_SIXTEENTH_SIMD_WIDTH:
                    return scanner[width](base + candidate_count - width, 0)
                return scanner[0](base + scanned, base + candidate_count)
            return False

    return scanner[0](base, base + candidate_count)


@always_inline
def _consume_simd_width_ladder(
    limit: Int,
    mut offset: Int,
    scanner: Some[def[width: Int](offset: Int) -> Bool],
) -> Bool:
    """Consume complete SIMD blocks and leave the scalar-tail offset."""
    comptime widths = [
        CLASS_SIMD_WIDTH,
        CLASS_TAIL_SIMD_WIDTH,
        CLASS_QUARTER_SIMD_WIDTH,
        CLASS_EIGHTH_SIMD_WIDTH,
    ]
    comptime for width in widths:
        while offset + width <= limit:
            if scanner[width](offset):
                return True
            offset += width
    return False
