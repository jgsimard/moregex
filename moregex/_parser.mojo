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


@always_inline
def _append_range(
    mut lows: List[Int], mut highs: List[Int], low: Int, high: Int
):
    for i in range(len(lows)):
        if low <= highs[i] + 1 and lows[i] <= high + 1:
            lows[i] = min(lows[i], low)
            highs[i] = max(highs[i], high)
            return
    lows.append(low)
    highs.append(high)


@always_inline
def _is_repeat_operator(ch: Int) -> Bool:
    return ch == ord("*") or ch == ord("+") or ch == ord("?") or ch == ord("{")


def _same_bracket_class(
    left: BracketClassNode, right: BracketClassNode
) -> Bool:
    if left.negated != right.negated or left.count != right.count:
        return False
    for i in range(left.count):
        if left.lows[i] != right.lows[i] or left.highs[i] != right.highs[i]:
            return False
    return True


def _byte_sequence_cardinality(nodes: List[RegexNode], node_index: Int) -> Int:
    """Return the number of byte strings represented by a bracket sequence."""
    ref sequence = nodes[node_index][SequenceNode]
    var cardinality = 1
    for i in range(sequence.count):
        ref bracket = nodes[sequence.items[i]][BracketClassNode]
        var choices = 0
        for item in range(bracket.count):
            choices += bracket.highs[item] - bracket.lows[item] + 1
        cardinality *= choices
    return cardinality


def _append_without_captures(
    nodes: List[RegexNode], node_index: Int, mut result: List[RegexNode]
) -> Int:
    """Copy an AST while removing capture-only wrapper nodes."""
    ref node = nodes[node_index]
    if node.isa[CaptureNode]():
        return _append_without_captures(nodes, node[CaptureNode].child, result)

    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        var child = _append_without_captures(nodes, repeat.child, result)
        result.append(
            RepeatNode(child, repeat.minimum, repeat.maximum, repeat.greedy)
        )
    elif node.isa[SequenceNode]():
        ref sequence = node[SequenceNode]
        var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
        for i in range(sequence.count):
            items[i] = _append_without_captures(
                nodes, sequence.items[i], result
            )
        result.append(SequenceNode(items, sequence.count))
    elif node.isa[OrNode]():
        ref alternation = node[OrNode]
        var options = StaticTuple[Int, MAX_BRANCHES]()
        for i in range(alternation.count):
            options[i] = _append_without_captures(
                nodes, alternation.options[i], result
            )
        result.append(OrNode(options, alternation.count))
    elif node.isa[EmptyNode]():
        result.append(EmptyNode())
    elif node.isa[LiteralNode]():
        result.append(LiteralNode(node[LiteralNode].value))
    elif node.isa[CharClassNode]():
        result.append(CharClassNode(node[CharClassNode].kind))
    elif node.isa[BracketClassNode]():
        ref bracket = node[BracketClassNode]
        result.append(
            BracketClassNode(
                bracket.lows, bracket.highs, bracket.count, bracket.negated
            )
        )
    else:
        result.append(ZeroWidthNode(node[ZeroWidthNode].kind))
    return len(result) - 1


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
            if self.peek_byte() != ord(")"):
                raise Error("expected closing parenthesis")
            _ = self.advance_byte()
            return self.add(CaptureNode(child, capture_index))

        _ = self.advance_byte()
        if self.peek_byte() == ord(":"):
            _ = self.advance_byte()
            var child = self.parse_or()
            if self.peek_byte() != ord(")"):
                raise Error("expected closing parenthesis")
            _ = self.advance_byte()
            return child

        var old_case_insensitive = self.case_insensitive
        var old_dot_all = self.dot_all
        var old_multi_line = self.multi_line
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
        if self.peek_byte() != ord(")"):
            raise Error("expected closing parenthesis")
        _ = self.advance_byte()
        self.case_insensitive = old_case_insensitive
        self.dot_all = old_dot_all
        self.multi_line = old_multi_line
        return child

    def parse(mut self) raises -> Int:
        var root = self.parse_or()
        if self.pos != self.pattern.byte_length():
            raise Error(String(t"unexpected '{self.peek_codepoint()}'"))
        root = self._normalize_literal_cartesian(root)
        if (
            self.unicode
            and self.pattern.find("][") >= 0
            and self.pattern.find("|") >= 0
        ):
            root = self._normalize_utf8_repeat_classes(root)
            root = self._normalize_root_utf8_repeat(root)
        return root

    def _normalize_literal_cartesian(mut self, root_index: Int) -> Int:
        """Factor a complete ASCII literal product into a bracket sequence."""
        ref root_node = self.nodes[root_index]
        if not root_node.isa[OrNode]():
            return root_index
        var alternation = root_node[OrNode]
        if alternation.count < 2:
            return root_index
        ref first_node = self.nodes[alternation.options[0]]
        if not first_node.isa[LiteralNode]():
            return root_index
        var byte_length = first_node[LiteralNode].value.byte_length()
        if byte_length == 0 or byte_length > MAX_SEQUENCE_ITEMS:
            return root_index
        for option in range(alternation.count):
            ref node = self.nodes[alternation.options[option]]
            if (
                not node.isa[LiteralNode]()
                or node[LiteralNode].value.byte_length() != byte_length
            ):
                return root_index
            for position in range(byte_length):
                if Int(node[LiteralNode].value.as_bytes()[position]) >= 128:
                    return root_index
            for prior in range(option):
                ref prior_node = self.nodes[alternation.options[prior]][
                    LiteralNode
                ]
                if node[LiteralNode].value == prior_node.value:
                    return root_index

        var product = 1
        for position in range(byte_length):
            var values = List[Int]()
            for option in range(alternation.count):
                ref literal = self.nodes[alternation.options[option]][
                    LiteralNode
                ]
                var value = Int(literal.value.as_bytes()[position])
                var present = False
                for existing in values:
                    present = present or existing == value
                if not present:
                    values.append(value)
            product *= len(values)
            if product > alternation.count:
                return root_index
        if product != alternation.count:
            return root_index

        var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
        for position in range(byte_length):
            var lows = List[Int]()
            var highs = List[Int]()
            for option in range(alternation.count):
                ref literal = self.nodes[alternation.options[option]][
                    LiteralNode
                ]
                var value = Int(literal.value.as_bytes()[position])
                _append_range(lows, highs, value, value)
            if len(lows) > MAX_CLASS_RANGES:
                return root_index
            var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
            var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
            for item in range(len(lows)):
                static_lows[item] = lows[item]
                static_highs[item] = highs[item]
            items[position] = self.add(
                BracketClassNode(static_lows, static_highs, len(lows), False)
            )
        if byte_length == 1:
            return items[0]
        return self.add(SequenceNode(items, byte_length))

    def _normalize_utf8_class_or(mut self, child_index: Int) -> Int:
        """Merge sibling one-byte brackets in one UTF-8 class alternation."""
        ref child_node = self.nodes[child_index]
        if not child_node.isa[OrNode]():
            return child_index
        var alternation = child_node[OrNode]
        var bracket_count = 0
        var has_sequence = False
        var lows = List[Int]()
        var highs = List[Int]()
        for i in range(alternation.count):
            ref option = self.nodes[alternation.options[i]]
            if option.isa[BracketClassNode]():
                ref bracket = option[BracketClassNode]
                if bracket.negated:
                    return child_index
                bracket_count += 1
                for item in range(bracket.count):
                    _append_range(
                        lows,
                        highs,
                        bracket.lows[item],
                        bracket.highs[item],
                    )
            elif option.isa[SequenceNode]():
                has_sequence = True
            else:
                return child_index
        if (
            bracket_count < 2
            or not has_sequence
            or len(lows) > MAX_CLASS_RANGES
        ):
            return child_index

        var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
        var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
        for i in range(len(lows)):
            static_lows[i] = lows[i]
            static_highs[i] = highs[i]
        var merged = self.add(
            BracketClassNode(static_lows, static_highs, len(lows), False)
        )
        var options = StaticTuple[Int, MAX_BRANCHES]()
        var count = 0
        var emitted_bracket = False
        for i in range(alternation.count):
            var option_index = alternation.options[i]
            if self.nodes[option_index].isa[BracketClassNode]():
                if not emitted_bracket:
                    options[count] = merged
                    count += 1
                    emitted_bracket = True
            else:
                options[count] = option_index
                count += 1
        return self.add(OrNode(options, count))

    def _normalize_utf8_repeat(mut self, repeat_index: Int) -> Int:
        ref node = self.nodes[repeat_index]
        if not node.isa[RepeatNode]():
            return repeat_index
        var repeat = node[RepeatNode]
        var child = self._normalize_utf8_class_or(repeat.child)
        if child == repeat.child:
            return repeat_index
        return self.add(
            RepeatNode(
                child,
                repeat.minimum,
                repeat.maximum,
                repeat.greedy,
            )
        )

    def _normalize_utf8_repeat_classes(mut self, root_index: Int) -> Int:
        """Normalize UTF-8 class repeats at the top execution level."""
        ref root = self.nodes[root_index]
        if root.isa[RepeatNode]():
            return self._normalize_utf8_repeat(root_index)
        if not root.isa[SequenceNode]():
            return root_index
        var sequence = root[SequenceNode]
        var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
        var changed = False
        for i in range(sequence.count):
            items[i] = self._normalize_utf8_repeat(sequence.items[i])
            changed = changed or items[i] != sequence.items[i]
        if not changed:
            return root_index
        return self.add(SequenceNode(items, sequence.count))

    def _normalize_root_utf8_repeat(mut self, root_index: Int) -> Int:
        """Factor equal lead-byte classes in a root UTF-8 class repeat."""
        ref root_node = self.nodes[root_index]
        if not root_node.isa[RepeatNode]():
            return root_index
        var repeat = root_node[RepeatNode]
        ref child_node = self.nodes[repeat.child]
        if not child_node.isa[OrNode]():
            return root_index
        var alternation = child_node[OrNode]
        for i in range(alternation.count):
            ref option = self.nodes[alternation.options[i]]
            if option.isa[BracketClassNode]():
                continue
            if not option.isa[SequenceNode]():
                return root_index
            ref sequence = option[SequenceNode]
            if sequence.count != 2:
                return root_index
            if (
                not self.nodes[sequence.items[0]].isa[BracketClassNode]()
                or not self.nodes[sequence.items[1]].isa[BracketClassNode]()
            ):
                return root_index

        var used = List[Bool]()
        for _ in range(alternation.count):
            used.append(False)
        var factored = List[Int]()
        var changed = False
        for i in range(alternation.count):
            if used[i]:
                continue
            var option_index = alternation.options[i]
            ref option = self.nodes[option_index]
            if option.isa[BracketClassNode]():
                factored.append(option_index)
                continue
            ref sequence = option[SequenceNode]
            var first_index = sequence.items[0]
            ref first = self.nodes[first_index][BracketClassNode]
            ref second = self.nodes[sequence.items[1]][BracketClassNode]
            if first.negated or second.negated:
                factored.append(option_index)
                continue
            var members = List[Int]()
            members.append(i)
            var lows = List[Int]()
            var highs = List[Int]()
            for item in range(second.count):
                _append_range(
                    lows, highs, second.lows[item], second.highs[item]
                )
            for j in range(i + 1, alternation.count):
                if used[j]:
                    continue
                ref candidate_node = self.nodes[alternation.options[j]]
                if not candidate_node.isa[SequenceNode]():
                    continue
                ref candidate = candidate_node[SequenceNode]
                ref candidate_first = self.nodes[candidate.items[0]][
                    BracketClassNode
                ]
                ref candidate_second = self.nodes[candidate.items[1]][
                    BracketClassNode
                ]
                if candidate_second.negated or not _same_bracket_class(
                    first, candidate_first
                ):
                    continue
                members.append(j)
                for item in range(candidate_second.count):
                    _append_range(
                        lows,
                        highs,
                        candidate_second.lows[item],
                        candidate_second.highs[item],
                    )
            if len(members) == 1 or len(lows) > MAX_CLASS_RANGES:
                factored.append(option_index)
                continue
            changed = True
            for member in members:
                used[member] = True
            var static_lows = StaticTuple[Int, MAX_CLASS_RANGES]()
            var static_highs = StaticTuple[Int, MAX_CLASS_RANGES]()
            for item in range(len(lows)):
                static_lows[item] = lows[item]
                static_highs[item] = highs[item]
            var suffix_index = self.add(
                BracketClassNode(static_lows, static_highs, len(lows), False)
            )
            var items = StaticTuple[Int, MAX_SEQUENCE_ITEMS]()
            items[0] = first_index
            items[1] = suffix_index
            factored.append(self.add(SequenceNode(items, 2)))
        # Equal-width byte-sequence alternatives have identical observable
        # matching behavior. Test broader ranges first so common Unicode
        # blocks do not pay for narrow exceptional branches on every scalar.
        for i in range(len(factored)):
            if not self.nodes[factored[i]].isa[SequenceNode]():
                continue
            var best = i
            var best_cardinality = _byte_sequence_cardinality(
                self.nodes, factored[i]
            )
            for j in range(i + 1, len(factored)):
                if not self.nodes[factored[j]].isa[SequenceNode]():
                    continue
                var cardinality = _byte_sequence_cardinality(
                    self.nodes, factored[j]
                )
                if cardinality > best_cardinality:
                    best = j
                    best_cardinality = cardinality
            if best != i:
                var current = factored[i]
                factored[i] = factored[best]
                factored[best] = current
                changed = True
        if not changed:
            return root_index
        var options = StaticTuple[Int, MAX_BRANCHES]()
        for i in range(len(factored)):
            options[i] = factored[i]
        var child_index = self.add(OrNode(options, len(factored)))
        return self.add(
            RepeatNode(
                child_index,
                repeat.minimum,
                repeat.maximum,
                repeat.greedy,
            )
        )

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
                if escaped == ord("d"):
                    _append_range(lows, highs, ord("0"), ord("9"))
                    continue
                if escaped == ord("w"):
                    _append_range(lows, highs, ord("a"), ord("z"))
                    _append_range(lows, highs, ord("A"), ord("Z"))
                    _append_range(lows, highs, ord("0"), ord("9"))
                    _append_range(lows, highs, ord("_"), ord("_"))
                    continue
                if escaped == ord("s"):
                    _append_range(lows, highs, ord(" "), ord(" "))
                    _append_range(lows, highs, ord("\t"), ord("\t"))
                    _append_range(lows, highs, ord("\n"), ord("\n"))
                    _append_range(lows, highs, ord("\r"), ord("\r"))
                    continue
                if escaped == ord("D"):
                    _append_range(lows, highs, 0, ord("0") - 1)
                    _append_range(lows, highs, ord("9") + 1, 255)
                    continue
                if escaped == ord("W"):
                    _append_range(lows, highs, 0, ord("0") - 1)
                    _append_range(lows, highs, ord("9") + 1, ord("A") - 1)
                    _append_range(lows, highs, ord("Z") + 1, ord("_") - 1)
                    _append_range(lows, highs, ord("_") + 1, ord("a") - 1)
                    _append_range(lows, highs, ord("z") + 1, 255)
                    continue
                if escaped == ord("S"):
                    _append_range(lows, highs, 0, ord("\t") - 1)
                    _append_range(lows, highs, ord("\n") + 1, ord("\r") - 1)
                    _append_range(lows, highs, ord("\r") + 1, ord(" ") - 1)
                    _append_range(lows, highs, ord(" ") + 1, 255)
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
            if escaped == "w":
                return self.add(CharClassNode(CHAR_ASCII_WORD))
            if escaped == "d":
                return self.add(CharClassNode(CHAR_ASCII_DIGIT))
            if escaped == "s":
                return self.add(CharClassNode(CHAR_ASCII_WHITESPACE))
            if escaped == "W":
                return self.add(CharClassNode(CHAR_ASCII_NON_WORD))
            if escaped == "D":
                return self.add(CharClassNode(CHAR_ASCII_NON_DIGIT))
            if escaped == "S":
                return self.add(CharClassNode(CHAR_ASCII_NON_WHITESPACE))
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
