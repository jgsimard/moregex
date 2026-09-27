"""Compile-time regex parser."""

from std.utils import StaticTuple


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
    CaptureNode,
    CharClassNode,
    EmptyNode,
    LiteralNode,
    MAX_BRANCHES,
    MAX_CLASS_RANGES,
    MAX_CAPTURE_GROUPS,
    MAX_SEQUENCE_ITEMS,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)

from ._normalization import _append_range, _normalize_regex_ast


@always_inline
def _is_repeat_operator(ch: Int) -> Bool:
    return ch == ord("*") or ch == ord("+") or ch == ord("?") or ch == ord("{")


@always_inline
def _escaped_class_kind(ch: Int) -> Int:
    if ch == ord("w"):
        return CHAR_ASCII_WORD
    if ch == ord("d"):
        return CHAR_ASCII_DIGIT
    if ch == ord("s"):
        return CHAR_ASCII_WHITESPACE
    if ch == ord("W"):
        return CHAR_ASCII_NON_WORD
    if ch == ord("D"):
        return CHAR_ASCII_NON_DIGIT
    if ch == ord("S"):
        return CHAR_ASCII_NON_WHITESPACE
    return -1


def _append_class_kind_ranges(
    mut lows: List[Int], mut highs: List[Int], kind: Int
):
    if kind == CHAR_ASCII_WORD:
        _append_range(lows, highs, ord("a"), ord("z"))
        _append_range(lows, highs, ord("A"), ord("Z"))
        _append_range(lows, highs, ord("0"), ord("9"))
        _append_range(lows, highs, ord("_"), ord("_"))
    elif kind == CHAR_ASCII_DIGIT:
        _append_range(lows, highs, ord("0"), ord("9"))
    elif kind == CHAR_ASCII_WHITESPACE:
        _append_range(lows, highs, ord(" "), ord(" "))
        _append_range(lows, highs, ord("\t"), ord("\t"))
        _append_range(lows, highs, ord("\n"), ord("\n"))
        _append_range(lows, highs, ord("\r"), ord("\r"))
    elif kind == CHAR_ASCII_NON_DIGIT:
        _append_range(lows, highs, 0, ord("0") - 1)
        _append_range(lows, highs, ord("9") + 1, 255)
    elif kind == CHAR_ASCII_NON_WORD:
        _append_range(lows, highs, 0, ord("0") - 1)
        _append_range(lows, highs, ord("9") + 1, ord("A") - 1)
        _append_range(lows, highs, ord("Z") + 1, ord("_") - 1)
        _append_range(lows, highs, ord("_") + 1, ord("a") - 1)
        _append_range(lows, highs, ord("z") + 1, 255)
    else:
        _append_range(lows, highs, 0, ord("\t") - 1)
        _append_range(lows, highs, ord("\n") + 1, ord("\r") - 1)
        _append_range(lows, highs, ord("\r") + 1, ord(" ") - 1)
        _append_range(lows, highs, ord(" ") + 1, 255)


@fieldwise_init
struct _ParserFlags(TrivialRegisterPassable):
    var case_insensitive: Bool
    var dot_all: Bool
    var multi_line: Bool


struct _Parser(Movable):
    var pattern: String
    var case_insensitive: Bool
    var unicode: Bool
    var dot_all: Bool
    var multi_line: Bool
    var pos: Int
    var nodes: List[RegexNode]
    var capture_count: Int

    def __init__(
        out self, pattern: String, case_insensitive: Bool, unicode: Bool
    ):
        self.pattern = pattern
        self.case_insensitive = case_insensitive
        self.unicode = unicode
        self.dot_all = False
        self.multi_line = False
        self.pos = 0
        self.nodes = List[RegexNode]()
        self.capture_count = 0

    def __moveinit__(out self, deinit existing: Self):
        self.pattern = existing.pattern^
        self.case_insensitive = existing.case_insensitive
        self.unicode = existing.unicode
        self.dot_all = existing.dot_all
        self.multi_line = existing.multi_line
        self.pos = existing.pos
        self.nodes = existing.nodes^
        self.capture_count = existing.capture_count

    @always_inline
    def peek_byte(self) -> Int:
        """Return the next pattern byte, or -1 at end of input."""
        if self.pos >= self.pattern.byte_length():
            return -1
        return Int(self.pattern.as_bytes()[self.pos])

    @always_inline
    def peek_byte_offset(self, offset: Int) -> Int:
        var index = self.pos + offset
        if index >= self.pattern.byte_length():
            return -1
        return Int(self.pattern.as_bytes()[index])

    @always_inline
    def codepoint_width_at(self, index: Int) -> Int:
        var first = Int(self.pattern.as_bytes()[index])
        var width = 1
        if first >= 0xF0:
            width = 4
        elif first >= 0xE0:
            width = 3
        elif first >= 0xC0:
            width = 2
        return width

    def peek_codepoint(
        self,
    ) -> type_of(self.pattern[byte = self.pos : self.pos]):
        if self.pos >= self.pattern.byte_length():
            return self.pattern[byte = self.pos : self.pos]
        var width = self.codepoint_width_at(self.pos)
        return self.pattern[byte = self.pos : self.pos + width]

    def advance_codepoint(
        mut self,
    ) -> type_of(self.peek_codepoint()):
        var start = self.pos
        var width = self.codepoint_width_at(start)
        self.pos += width
        return self.pattern[byte = start : start + width]

    @always_inline
    def advance_byte(mut self) -> Int:
        var value = self.peek_byte()
        if value >= 0:
            self.pos += 1
        return value

    def add(mut self, var node: RegexNode) -> Int:
        self.nodes.append(node^)
        return len(self.nodes) - 1

    @always_inline
    def flags(self) -> _ParserFlags:
        return _ParserFlags(
            self.case_insensitive,
            self.dot_all,
            self.multi_line,
        )

    @always_inline
    def restore_flags(mut self, flags: _ParserFlags):
        self.case_insensitive = flags.case_insensitive
        self.dot_all = flags.dot_all
        self.multi_line = flags.multi_line

    @always_inline
    def finish_group(mut self) raises:
        if self.peek_byte() != ord(")"):
            raise Error("expected closing parenthesis")
        _ = self.advance_byte()

    def is_ascii_letter(self, ch: Int) -> Bool:
        var folded = ch | 0x20
        return ord("a") <= folded <= ord("z")

    def add_literal(mut self, ch: String) -> Int:
        if self.case_insensitive and self.is_ascii_letter(ord(ch)):
            var value = ord(ch) | 0x20
            var lows = StaticTuple[Int, MAX_CLASS_RANGES]()
            var highs = StaticTuple[Int, MAX_CLASS_RANGES]()
            lows[0] = value
            highs[0] = value
            lows[1] = value - (ord("a") - ord("A"))
            highs[1] = lows[1]
            return self.add(BracketClassNode(lows, highs, 2, False))
        return self.add(LiteralNode(ch))

    def parse_group(mut self) raises -> Int:
        """Parse a capturing-equivalent or inline-flag group after `(`."""
        if self.peek_byte() != ord("?"):
            self.capture_count += 1
            if self.capture_count > MAX_CAPTURE_GROUPS:
                raise Error("too many capture groups")
            var capture_index = self.capture_count
            var child = self.parse_or()
            self.finish_group()
            return self.add(CaptureNode(child, capture_index))

        _ = self.advance_byte()
        if self.peek_byte() == ord(":"):
            _ = self.advance_byte()
            var child = self.parse_or()
            self.finish_group()
            return child

        var old_flags = self.flags()
        var flag_count = 0
        while True:
            var flag = self.peek_byte()
            if flag == ord("i"):
                self.case_insensitive = True
            elif flag == ord("s"):
                self.dot_all = True
            elif flag == ord("m"):
                self.multi_line = True
            else:
                break
            _ = self.advance_byte()
            flag_count += 1
        if flag_count == 0:
            raise Error("unsupported group extension")

        if self.peek_byte() == ord(")"):
            _ = self.advance_byte()
            return self.add(EmptyNode())
        if self.peek_byte() != ord(":"):
            raise Error("expected ':' or ')' after inline flags")
        _ = self.advance_byte()

        var child = self.parse_or()
        self.finish_group()
        self.restore_flags(old_flags)
        return child

    def parse(mut self) raises -> Int:
        var root = self.parse_or()
        if self.pos != self.pattern.byte_length():
            raise Error(String(t"unexpected '{self.peek_codepoint()}'"))
        root = _normalize_regex_ast(self.nodes, root, self.unicode)
        return root

    def parse_or(mut self) raises -> Int:
        var options = List[Int]()
        options.append(self.parse_sequence())
        while self.peek_byte() == ord("|"):
            _ = self.advance_byte()
            options.append(self.parse_sequence())

        if len(options) == 1:
            return options[0]
        if len(options) > MAX_BRANCHES:
            raise Error("too many alternation branches")

        var values = StaticTuple[Int, MAX_BRANCHES]()
        for i in range(len(options)):
            values[i] = options[i]
        return self.add(OrNode(values, len(options)))

    def parse_sequence(mut self) raises -> Int:
        var items = List[Int]()
        while True:
            var ch = self.peek_byte()
            if ch < 0 or ch == ord("|") or ch == ord(")"):
                break
            items.append(self.parse_repeat())

        if len(items) == 0:
            return self.add(EmptyNode())
        if len(items) == 1:
            return items[0]
        if len(items) > MAX_SEQUENCE_ITEMS:
            raise Error("sequence is too long")

        var values = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
        for i in range(len(items)):
            values[i] = items[i]
        return self.add(SequenceNode(values, len(items)))

    def parse_repeat(mut self) raises -> Int:
        var child = self.parse_primary()
        var ch = self.peek_byte()
        if _is_repeat_operator(ch) and self.nodes[child].isa[ZeroWidthNode]():
            raise Error("a zero-width assertion cannot be repeated")
        if ch == ord("*"):
            _ = self.advance_byte()
            return self.add_repeat(child, 0, -1)
        if ch == ord("+"):
            _ = self.advance_byte()
            return self.add_repeat(child, 1, -1)
        if ch == ord("?"):
            _ = self.advance_byte()
            return self.add_repeat(child, 0, 1)
        if ch == ord("{"):
            _ = self.advance_byte()
            var minimum = self.parse_number()
            var maximum = minimum
            if self.peek_byte() == ord(","):
                _ = self.advance_byte()
                if self.peek_byte() == ord("}"):
                    maximum = -1
                else:
                    maximum = self.parse_number()
            if self.peek_byte() != ord("}"):
                raise Error("expected closing brace in repetition")
            _ = self.advance_byte()
            if maximum >= 0 and minimum > maximum:
                raise Error("repetition minimum exceeds maximum")
            return self.add_repeat(child, minimum, maximum)
        return child

    def add_repeat(mut self, child: Int, minimum: Int, maximum: Int) -> Int:
        var greedy = True
        if self.peek_byte() == ord("?"):
            _ = self.advance_byte()
            greedy = False
        return self.add(RepeatNode(child, minimum, maximum, greedy))

    def parse_number(mut self) raises -> Int:
        if not (ord("0") <= self.peek_byte() <= ord("9")):
            raise Error("expected a repetition count")
        var value = 0
        while ord("0") <= self.peek_byte() <= ord("9"):
            value = value * 10 + self.advance_byte() - ord("0")
            if value > 1_000_000:
                raise Error("repetition count is too large")
        return value

    def hex_digit_value(self, ch: Int) raises -> Int:
        if ord("0") <= ch <= ord("9"):
            return ch - ord("0")
        if ord("a") <= ch <= ord("f"):
            return ch - ord("a") + 10
        if ord("A") <= ch <= ord("F"):
            return ch - ord("A") + 10
        raise Error("expected a hexadecimal digit")

    def parse_hex_byte(mut self) raises -> Int:
        var first = self.advance_byte()
        var second = self.advance_byte()
        if first < 0 or second < 0:
            raise Error("incomplete hexadecimal byte escape")
        return self.hex_digit_value(first) * 16 + self.hex_digit_value(second)

    def parse_escaped_byte(mut self, escaped: Int) raises -> Int:
        if escaped == ord("x"):
            return self.parse_hex_byte()
        if escaped == ord("n"):
            return ord("\n")
        if escaped == ord("r"):
            return ord("\r")
        if escaped == ord("t"):
            return ord("\t")
        return escaped

    def parse_bracket_class(mut self) raises -> Int:
        # Opening '[' has already been consumed.
        var negated = False
        if self.peek_byte() == ord("^"):
            negated = True
            _ = self.advance_byte()

        var lows = List[Int]()
        var highs = List[Int]()
        while self.peek_byte() != ord("]"):
            if self.peek_byte() < 0:
                raise Error("expected closing bracket")

            var first = self.advance_codepoint()
            var low: Int
            if first == "\\":
                if self.peek_byte() < 0:
                    raise Error("incomplete escape in bracket class")
                var escaped = ord(self.advance_codepoint())
                var class_kind = _escaped_class_kind(escaped)
                if class_kind >= 0:
                    _append_class_kind_ranges(lows, highs, class_kind)
                    continue
                low = self.parse_escaped_byte(escaped)
            else:
                low = ord(first)

            var high = low
            if self.peek_byte() == ord("-") and self.peek_byte_offset(1) != ord(
                "]"
            ):
                _ = self.advance_byte()
                if self.peek_byte() < 0:
                    raise Error("expected range endpoint")
                var last = self.advance_codepoint()
                if last == "]":
                    raise Error("expected range endpoint")
                if last == "\\":
                    if self.peek_byte() < 0:
                        raise Error("expected range endpoint")
                    var escaped_last = ord(self.advance_codepoint())
                    if (
                        escaped_last == ord("d")
                        or escaped_last == ord("w")
                        or escaped_last == ord("s")
                    ):
                        raise Error("invalid range endpoint")
                    high = self.parse_escaped_byte(escaped_last)
                else:
                    high = ord(last)
                if low > high:
                    raise Error("descending bracket range")
            _append_range(lows, highs, low, high)
            if self.case_insensitive:
                var upper_low = max(low, ord("A"))
                var upper_high = min(high, ord("Z"))
                if upper_low <= upper_high:
                    _append_range(
                        lows,
                        highs,
                        upper_low + ord("a") - ord("A"),
                        upper_high + ord("a") - ord("A"),
                    )
                var lower_low = max(low, ord("a"))
                var lower_high = min(high, ord("z"))
                if lower_low <= lower_high:
                    _append_range(
                        lows,
                        highs,
                        lower_low - (ord("a") - ord("A")),
                        lower_high - (ord("a") - ord("A")),
                    )

        if len(lows) == 0:
            raise Error("empty bracket class")
        _ = self.advance_byte()
        if len(lows) > MAX_CLASS_RANGES:
            raise Error("too many bracket class ranges")

        var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
        var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
        for i in range(len(lows)):
            static_lows[i] = lows[i]
            static_highs[i] = highs[i]
        return self.add(
            BracketClassNode(static_lows, static_highs, len(lows), negated)
        )

    def parse_primary(mut self) raises -> Int:
        var first = self.peek_byte()
        if first == ord("("):
            _ = self.advance_byte()
            return self.parse_group()

        if first == ord("["):
            _ = self.advance_byte()
            return self.parse_bracket_class()

        if first == ord("."):
            _ = self.advance_byte()
            if self.unicode:
                if self.dot_all:
                    return self.add(CharClassNode(CHAR_UNICODE_DOTALL))
                return self.add(CharClassNode(CHAR_UNICODE_DOT))
            if self.dot_all:
                return self.add(CharClassNode(CHAR_BYTE_DOTALL))
            return self.add(CharClassNode(CHAR_BYTE_DOT))

        if first == ord("^"):
            _ = self.advance_byte()
            if self.multi_line:
                return self.add(ZeroWidthNode(ASSERT_LINE_START))
            return self.add(ZeroWidthNode(ASSERT_INPUT_START))

        if first == ord("$"):
            _ = self.advance_byte()
            if self.multi_line:
                return self.add(ZeroWidthNode(ASSERT_LINE_END))
            return self.add(ZeroWidthNode(ASSERT_INPUT_END))

        if first == ord("\\"):
            _ = self.advance_byte()
            if self.peek_byte() < 0:
                raise Error("incomplete escape")
            var escaped = self.advance_codepoint()
            var class_kind = _escaped_class_kind(ord(escaped))
            if class_kind >= 0:
                return self.add(CharClassNode(class_kind))
            if escaped == "b":
                return self.add(ZeroWidthNode(ASSERT_WORD_BOUNDARY))
            if escaped == "B":
                return self.add(ZeroWidthNode(ASSERT_NON_WORD_BOUNDARY))
            if escaped == "n":
                return self.add(LiteralNode("\n"))
            if escaped == "r":
                return self.add(LiteralNode("\r"))
            if escaped == "t":
                return self.add(LiteralNode("\t"))
            return self.add_literal(String(escaped))

        if (
            first < 0
            or first == ord("|")
            or first == ord(")")
            or _is_repeat_operator(first)
            or first == ord("}")
            or first == ord("]")
        ):
            raise Error("expected a literal, group, wildcard, or class")

        if self.case_insensitive and self.is_ascii_letter(first):
            return self.add_literal(String(self.advance_codepoint()))

        # Coalesce adjacent literals, except when the final literal is quantified.
        var literal = String()
        literal += self.advance_codepoint()
        if _is_repeat_operator(self.peek_byte()):
            return self.add(LiteralNode(literal))

        while True:
            first = self.peek_byte()
            if (
                first < 0
                or first == ord("|")
                or first == ord(")")
                or _is_repeat_operator(first)
                or first == ord("}")
                or first == ord("]")
                or first == ord("(")
                or first == ord(".")
                or first == ord("\\")
                or first == ord("[")
                or first == ord("^")
                or first == ord("$")
            ):
                break
            if self.case_insensitive and self.is_ascii_letter(first):
                break
            var width = self.codepoint_width_at(self.pos)
            if self.pos + width < self.pattern.byte_length():
                var after = self.peek_byte_offset(width)
                if _is_repeat_operator(after):
                    break
            literal += self.advance_codepoint()
        return self.add(LiteralNode(literal))
