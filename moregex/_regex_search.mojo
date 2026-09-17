"""Specialized regex search kernels."""

from ._ast import (
    ASSERT_WORD_BOUNDARY,
    CHAR_ASCII_DIGIT,
    CHAR_ASCII_WORD,
    BracketClassNode,
    CharClassNode,
    LiteralNode,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.math import iota
from std.memory import pack_bits
from std.sys import CompilationTarget, llvm_intrinsic, simd_width_of
from std.sys.intrinsics import masked_load

from ._regex_common import (
    CLASS_SIMD_WIDTH,
    _bracket_accepts,
    _class_mask,
    _is_ascii_digit,
    _is_ascii_word,
    _match_checksum,
    _match_literal,
    _search_simd_width_ladder,
)

from ._regex_analysis import (
    _bracket_mask,
    _is_exact_bracket_node_range,
)

from ._regex_matcher import _match_node
from ._regex_count import _search_one_byte_run


def _is_unbounded_bracket_repeat[
    nodes: List[RegexNode], node: RegexNode
]() -> Bool:
    comptime child = _repeat_child_index[node, 1, -1]()
    comptime if child < 0:
        return False
    else:
        return comptime (nodes[child].isa[BracketClassNode]())


def _is_bracket_infix_search[nodes: List[RegexNode], root: RegexNode]() -> Bool:
    """Recognize `bracket+ one-byte-literal bracket+` at compile time."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 3:
            comptime center = nodes[sequence.items[1]]
            comptime if center.isa[LiteralNode]():
                comptime literal = center[LiteralNode]
                comptime if literal.value.byte_length() == 1:
                    comptime if _is_unbounded_bracket_repeat[
                        nodes, nodes[sequence.items[0]]
                    ]():
                        comptime if _is_unbounded_bracket_repeat[
                            nodes, nodes[sequence.items[2]]
                        ]():
                            comptime left_repeat = nodes[sequence.items[0]][
                                RepeatNode
                            ]
                            comptime left = nodes[left_repeat.child][
                                BracketClassNode
                            ]
                            comptime delimiter = Int(
                                literal.value.as_bytes()[0]
                            )
                            # Without backtracking, the left run must stop at
                            # the delimiter for this transform to be exact.
                            return not _bracket_accepts[left](delimiter)
    return False


@always_inline
def _bracket_infix_block_matches[
    nodes: List[RegexNode], root: RegexNode, width: Int, partial: Bool
](text: ImmStringSpan, offset: Int, count: Int) -> Bool:
    """Search one full or bounds-masked SIMD block."""
    comptime sequence = root[SequenceNode]
    comptime literal = nodes[sequence.items[1]][LiteralNode]
    comptime literal_byte = literal.value.as_bytes()[0]
    comptime left_repeat = nodes[sequence.items[0]][RepeatNode]
    comptime right_repeat = nodes[sequence.items[2]][RepeatNode]
    comptime left_class = nodes[left_repeat.child][BracketClassNode]
    comptime right_class = nodes[right_repeat.child][BracketClassNode]
    var pointer = text.unsafe_ptr()
    var active = SIMD[.bool, width](fill=True)
    var values: SIMD[.uint8, width]
    comptime if partial:
        var lanes = iota[DType.uint8, width]()
        active = lanes.lt(SIMD[.uint8, width](UInt8(count)))
        values = masked_load[width](
            pointer.unsafe_offset(offset), active, SIMD[.uint8, width](0)
        )
    else:
        values = pointer.unsafe_load[width=width, alignment=1](offset)
    var candidates = values.eq(SIMD[.uint8, width](literal_byte)) & active
    if not any(candidates):
        return False
    var left_values: SIMD[.uint8, width]
    comptime if partial:
        left_values = masked_load[width](
            pointer.unsafe_offset(offset - 1),
            candidates,
            SIMD[.uint8, width](0),
        )
    else:
        left_values = pointer.unsafe_load[width=width, alignment=1](offset - 1)
    candidates &= _bracket_mask[left_class, width](left_values)
    if not any(candidates):
        return False
    var right_values: SIMD[.uint8, width]
    comptime if partial:
        right_values = masked_load[width](
            pointer.unsafe_offset(offset + 1),
            candidates,
            SIMD[.uint8, width](0),
        )
    else:
        right_values = pointer.unsafe_load[width=width, alignment=1](offset + 1)
    candidates &= _bracket_mask[right_class, width](right_values)
    return any(candidates)


@always_inline
def _search_bracket_infix[
    nodes: List[RegexNode], root: RegexNode
](text: ImmStringSpan) -> Bool:
    """Search a bracket/literal/bracket infix via SIMD delimiter scans."""
    var length = text.byte_length()
    if length < 3:
        return False
    var candidate_count = length - 2
    var scanned = 0
    if candidate_count >= CLASS_SIMD_WIDTH:
        while scanned + CLASS_SIMD_WIDTH <= candidate_count:
            if _bracket_infix_block_matches[
                nodes, root, CLASS_SIMD_WIDTH, False
            ](text, 1 + scanned, CLASS_SIMD_WIDTH):
                return True
            scanned += CLASS_SIMD_WIDTH
        if scanned < candidate_count:
            return _bracket_infix_block_matches[
                nodes, root, CLASS_SIMD_WIDTH, True
            ](text, 1 + scanned, candidate_count - scanned)
        return False

    return _bracket_infix_block_matches[nodes, root, CLASS_SIMD_WIDTH, True](
        text, 1, candidate_count
    )


def _repeat_child_index[node: RegexNode, minimum: Int, maximum: Int]() -> Int:
    comptime if node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum == minimum and repeat.maximum == maximum:
            return repeat.child
    return -1


def _is_prefixed_infix_search[
    nodes: List[RegexNode], root: RegexNode
]() -> Bool:
    """Recognize `(bracket bracket*) literal bracket+ optional?`."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 3 or sequence.count == 4:
            comptime suffix_ok = sequence.count == 3 or _repeat_child_index[
                nodes[sequence.items[3]], 0, 1
            ]() >= 0
            comptime prefix_node = nodes[sequence.items[0]]
            comptime if suffix_ok and prefix_node.isa[SequenceNode]():
                comptime prefix = prefix_node[SequenceNode]
                comptime if prefix.count == 2:
                    comptime tail_child = _repeat_child_index[
                        nodes[prefix.items[1]], 0, -1
                    ]()
                    comptime if (
                        nodes[prefix.items[0]].isa[BracketClassNode]()
                        and tail_child >= 0
                        and nodes[tail_child].isa[BracketClassNode]()
                    ):
                        comptime center = nodes[sequence.items[1]]
                        comptime if center.isa[LiteralNode]():
                            comptime literal = center[LiteralNode]
                            comptime if (
                                literal.value.byte_length() > 0
                                and _is_unbounded_bracket_repeat[
                                    nodes, nodes[sequence.items[2]]
                                ]()
                            ):
                                comptime tail = nodes[tail_child][
                                    BracketClassNode
                                ]
                                # The greedy prefix must stop at the literal
                                # without requiring unsupported giveback.
                                return not _bracket_accepts[tail](
                                    ord(literal.value[byte=0])
                                )
    return False


@always_inline
def _prefixed_infix_prefix_matches[
    nodes: List[RegexNode], root: RegexNode
](text: ImmStringSpan, delimiter: Int) -> Bool:
    comptime sequence = root[SequenceNode]
    comptime prefix = nodes[sequence.items[0]][SequenceNode]
    comptime first_class = nodes[prefix.items[0]][BracketClassNode]
    comptime tail_repeat = nodes[prefix.items[1]][RepeatNode]
    comptime tail_class = nodes[tail_repeat.child][BracketClassNode]
    var bytes = text.as_bytes()
    var cursor = delimiter - 1
    while cursor >= 0:
        var value = Int(bytes[cursor])
        if _bracket_accepts[first_class](value):
            return True
        if not _bracket_accepts[tail_class](value):
            break
        cursor -= 1
    return False


@always_inline
def _prefixed_infix_matches_at[
    nodes: List[RegexNode], root: RegexNode
](text: ImmStringSpan, delimiter: Int) -> Bool:
    comptime sequence = root[SequenceNode]
    comptime literal = nodes[sequence.items[1]][LiteralNode]
    comptime right_repeat = nodes[sequence.items[2]][RepeatNode]
    comptime right_class = nodes[right_repeat.child][BracketClassNode]
    comptime literal_length = literal.value.byte_length()
    var length = text.byte_length()
    var bytes = text.as_bytes()
    var right = delimiter + literal_length
    if right >= length:
        return False
    if not _match_literal[literal.value](text, delimiter):
        return False
    if not _bracket_accepts[right_class](Int(bytes[right])):
        return False
    return _prefixed_infix_prefix_matches[nodes, root](text, delimiter)


@always_inline
def _prefixed_infix_block_matches[
    nodes: List[RegexNode], root: RegexNode, width: Int
](text: ImmStringSpan, offset: Int) -> Bool:
    comptime sequence = root[SequenceNode]
    comptime literal = nodes[sequence.items[1]][LiteralNode]
    comptime right_repeat = nodes[sequence.items[2]][RepeatNode]
    comptime right_class = nodes[right_repeat.child][BracketClassNode]
    comptime literal_length = literal.value.byte_length()
    var pointer = text.unsafe_ptr()
    var candidates = SIMD[.bool, width](fill=True)
    comptime for position in range(literal_length):
        var values = pointer.unsafe_load[width=width, alignment=1](
            offset + position
        )
        comptime expected = literal.value.as_bytes()[position]
        candidates &= values.eq(SIMD[.uint8, width](expected))
    var right_values = pointer.unsafe_load[width=width, alignment=1](
        offset + literal_length
    )
    candidates &= _bracket_mask[right_class, width](right_values)
    var pending = pack_bits(candidates)
    while pending != 0:
        var lane = Int(count_trailing_zeros(pending))
        pending &= pending - 1
        if _prefixed_infix_prefix_matches[nodes, root](text, offset + lane):
            return True
    return False


@always_inline
def _search_prefixed_infix[
    nodes: List[RegexNode], root: RegexNode
](text: ImmStringSpan) -> Bool:
    """SIMD-scan a mandatory literal and validate its variable prefix."""
    comptime sequence = root[SequenceNode]
    comptime literal = nodes[sequence.items[1]][LiteralNode]
    comptime literal_length = literal.value.byte_length()
    var length = text.byte_length()
    var candidate_count = length - literal_length - 1
    if candidate_count <= 0:
        return False

    @always_inline
    def scan[width: Int](start: Int, end: Int) {imm text} -> Bool:
        comptime if width == 0:
            for offset in range(start, end):
                if _prefixed_infix_matches_at[nodes, root](text, offset):
                    return True
            return False
        else:
            return _prefixed_infix_block_matches[nodes, root, width](
                text, start
            )

    return _search_simd_width_ladder(
        candidate_count,
        1,
        scan,
    )


@always_inline
def _grep_prefixed_infix[
    nodes: List[RegexNode], root: RegexNode
](text: String) -> Int:
    """Count matching lines by scanning the mandatory infix globally."""
    comptime sequence = root[SequenceNode]
    comptime literal = nodes[sequence.items[1]][LiteralNode]
    comptime literal_length = literal.value.byte_length()
    var length = text.byte_length()
    if length == 0:
        return 0

    var total = 0
    var line_start = 0
    var line_end = text.find("\n")
    if line_end < 0:
        line_end = length
    var search_start = 0
    while search_start < length:
        var delimiter = text.find(literal.value, search_start)
        if delimiter < 0:
            break
        while delimiter >= line_end and line_end < length:
            line_start = line_end + 1
            line_end = text.find("\n", line_start)
            if line_end < 0:
                line_end = length

        var content_end = line_end
        if (
            content_end > line_start
            and Int(text.as_bytes()[content_end - 1]) == 13
        ):
            content_end -= 1
        if (
            delimiter + literal_length < content_end
            and _prefixed_infix_matches_at[nodes, root](
                text[byte=line_start:content_end], delimiter - line_start
            )
        ):
            total += 1
            if line_end == length:
                break
            search_start = line_end + 1
        else:
            search_start = delimiter + 1
    return total


def _all_infix_options[nodes: List[RegexNode], alternation: OrNode]() -> Bool:
    comptime for i in range(alternation.count):
        comptime node = nodes[alternation.options[i]]
        comptime if not (
            _is_bracket_infix_search[nodes, node]()
            or _is_prefixed_infix_search[nodes, node]()
        ):
            return False
    return True


@always_inline
def _search_infix_alternation[
    nodes: List[RegexNode], alternation: OrNode
](text: ImmStringSpan) -> Bool:
    comptime for i in range(alternation.count):
        comptime node = nodes[alternation.options[i]]
        comptime if _is_bracket_infix_search[nodes, node]():
            if _search_bracket_infix[nodes, node](text):
                return True
        elif _is_prefixed_infix_search[nodes, node]():
            if _search_prefixed_infix[nodes, node](text):
                return True
    return False


def _is_word_boundary_node[node: RegexNode]() -> Bool:
    comptime if node.isa[ZeroWidthNode]():
        comptime if node[ZeroWidthNode].kind == ASSERT_WORD_BOUNDARY:
            return True
    return False


def _is_ascii_word_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[CharClassNode]():
        return node[CharClassNode].kind == CHAR_ASCII_WORD
    comptime if node.isa[BracketClassNode]():
        comptime bracket = node[BracketClassNode]
        comptime for value in range(256):
            comptime if _bracket_accepts[bracket](value) != _is_ascii_word(
                value
            ):
                return False
        return True
    return False


def _is_long_word_search[nodes: List[RegexNode], root: RegexNode]() -> Bool:
    """Recognize `\\b\\w{minimum,}\\b` at compile time."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 3:
            comptime if _is_word_boundary_node[nodes[sequence.items[0]]]():
                comptime middle = nodes[sequence.items[1]]
                comptime if middle.isa[RepeatNode]():
                    comptime repeat = middle[RepeatNode]
                    return (
                        repeat.minimum > 0
                        and repeat.maximum == -1
                        and _is_ascii_word_node[nodes, repeat.child]()
                        and _is_word_boundary_node[nodes[sequence.items[2]]]()
                    )
    return False


def _is_word_run_literal_suffix[
    nodes: List[RegexNode], root: RegexNode
]() -> Bool:
    """Recognize `\\b\\w{minimum,}literal\\b` with an ASCII-word literal."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 4:
            comptime repeat_node = nodes[sequence.items[1]]
            comptime literal_node = nodes[sequence.items[2]]
            comptime if (
                _is_word_boundary_node[nodes[sequence.items[0]]]()
                and repeat_node.isa[RepeatNode]()
                and literal_node.isa[LiteralNode]()
                and _is_word_boundary_node[nodes[sequence.items[3]]]()
            ):
                comptime repeat = repeat_node[RepeatNode]
                comptime literal = literal_node[LiteralNode]
                comptime if (
                    repeat.minimum > 0
                    and repeat.maximum == -1
                    and _is_ascii_word_node[nodes, repeat.child]()
                    and literal.value.byte_length() > 0
                ):
                    comptime for i in range(literal.value.byte_length()):
                        comptime if not _is_ascii_word(
                            Int(literal.value.as_bytes()[i])
                        ):
                            return False
                    return True
    return False


def _is_word_boundary_wrapped[
    nodes: List[RegexNode], root: RegexNode
]() -> Bool:
    """Recognize `\b expression \b` for boundary-only candidate scans."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 3:
            return (
                _is_word_boundary_node[nodes[sequence.items[0]]]()
                and _is_word_boundary_node[nodes[sequence.items[2]]]()
            )
    return False


def _node_starts_only_with_ascii_word[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Conservatively prove every match starts with an ASCII word byte."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        comptime literal = node[LiteralNode]
        comptime if literal.value.byte_length() == 0:
            return False
        return _is_ascii_word(Int(literal.value.as_bytes()[0]))
    elif node.isa[CharClassNode]():
        return node[CharClassNode].kind == CHAR_ASCII_WORD
    elif node.isa[BracketClassNode]():
        comptime bracket = node[BracketClassNode]
        comptime for value in range(256):
            comptime if _bracket_accepts[bracket](value):
                comptime if not _is_ascii_word(value):
                    return False
        return True
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for i in range(alternation.count):
            comptime if not _node_starts_only_with_ascii_word[
                nodes, alternation.options[i]
            ]():
                return False
        return True
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum == 0:
            return False
        return _node_starts_only_with_ascii_word[nodes, repeat.child]()
    elif node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 0:
            return False
        return _node_starts_only_with_ascii_word[nodes, sequence.items[0]]()
    return False


@always_inline
def _search_long_word[
    nodes: List[RegexNode], root: RegexNode
](text: ImmStringSpan) -> Bool:
    """Find a complete ASCII word run meeting the compile-time minimum."""
    comptime sequence = root[SequenceNode]
    comptime repeat = nodes[sequence.items[1]][RepeatNode]
    return _search_one_byte_run[nodes, repeat.child, repeat.minimum](text)


@always_inline
def _count_long_word[regex: Regex, sum_spans: Bool](text: ImmStringSpan) -> Int:
    """Count complete ASCII word runs that meet the minimum length."""
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime repeat = regex.nodes[root.items[1]][RepeatNode]
    var length = text.byte_length()
    var bytes = text.as_bytes()
    var total = 0
    var position = 0
    var run_length = 0
    while position + CLASS_SIMD_WIDTH <= length:
        var values = text.unsafe_ptr().unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](position)
        var nonword = pack_bits(
            _class_mask[CHAR_ASCII_WORD, CLASS_SIMD_WIDTH](values)
            ^ SIMD[.bool, CLASS_SIMD_WIDTH](fill=True)
        )
        var block_position = 0
        while nonword != 0:
            var lane = Int(count_trailing_zeros(nonword))
            nonword &= nonword - 1
            run_length += lane - block_position
            if run_length >= repeat.minimum:
                total += _match_checksum[sum_spans](run_length)
            run_length = 0
            block_position = lane + 1
        run_length += CLASS_SIMD_WIDTH - block_position
        position += CLASS_SIMD_WIDTH
    while position < length:
        if _is_ascii_word(Int(bytes[position])):
            run_length += 1
        else:
            if run_length >= repeat.minimum:
                total += _match_checksum[sum_spans](run_length)
            run_length = 0
        position += 1
    if run_length >= repeat.minimum:
        total += _match_checksum[sum_spans](run_length)
    return total


@always_inline
def _count_word_run_literal_suffix[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Drive a complete-word suffix match from its mandatory literal."""
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime repeat = regex.nodes[root.items[1]][RepeatNode]
    comptime literal = regex.nodes[root.items[2]][LiteralNode]
    comptime literal_length = literal.value.byte_length()
    var bytes = text.as_bytes()
    var length = text.byte_length()
    var total = 0
    var minimum_start = 0
    var candidate = text.find(literal.value)
    while candidate >= 0:
        var end = candidate + literal_length
        if end == length or not _is_ascii_word(Int(bytes[end])):
            var start = candidate
            while start > minimum_start and _is_ascii_word(
                Int(bytes[start - 1])
            ):
                start -= 1
            if candidate - start >= repeat.minimum and (
                start == 0 or not _is_ascii_word(Int(bytes[start - 1]))
            ):
                total += _match_checksum[sum_spans](end - start)
                minimum_start = end
                candidate = text.find(literal.value, end)
                continue
        candidate = text.find(literal.value, candidate + 1)
    return total


@always_inline
def _count_word_boundary_wrapped[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Evaluate a boundary-wrapped expression only at actual boundaries."""
    var length = text.byte_length()
    var bytes = text.as_bytes()
    var total = 0
    var next_start = 0
    var previous_is_word = False
    comptime root = regex.nodes[regex.root][SequenceNode]
    comptime starts_with_word = _node_starts_only_with_ascii_word[
        regex.nodes, root.items[1]
    ]()
    comptime if starts_with_word:
        if length > 0 and _is_ascii_word(Int(bytes[0])):
            var result = _match_node[regex.nodes, regex.root](text, 0)
            if result:
                var consumed = result.unsafe_value().consumed()
                total += _match_checksum[sum_spans](consumed)
                next_start = max(1, consumed)
        var position = 1
        while position + CLASS_SIMD_WIDTH <= length:
            var previous_values = text.unsafe_ptr().unsafe_load[
                width=CLASS_SIMD_WIDTH, alignment=1
            ](position - 1)
            var current_values = text.unsafe_ptr().unsafe_load[
                width=CLASS_SIMD_WIDTH, alignment=1
            ](position)
            var previous_words = _class_mask[CHAR_ASCII_WORD, CLASS_SIMD_WIDTH](
                previous_values
            )
            var current_words = _class_mask[CHAR_ASCII_WORD, CLASS_SIMD_WIDTH](
                current_values
            )
            var candidates = current_words & (
                previous_words ^ SIMD[.bool, CLASS_SIMD_WIDTH](fill=True)
            )
            var pending = pack_bits(candidates)
            while pending != 0:
                var lane = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                var start = position + lane
                if start >= next_start:
                    var result = _match_node[regex.nodes, regex.root](
                        text, start
                    )
                    if result:
                        var consumed = result.unsafe_value().consumed()
                        total += _match_checksum[sum_spans](consumed)
                        next_start = start + max(1, consumed)
            position += CLASS_SIMD_WIDTH
        while position < length:
            if (
                position >= next_start
                and _is_ascii_word(Int(bytes[position]))
                and not _is_ascii_word(Int(bytes[position - 1]))
            ):
                var result = _match_node[regex.nodes, regex.root](
                    text, position
                )
                if result:
                    var consumed = result.unsafe_value().consumed()
                    total += _match_checksum[sum_spans](consumed)
                    next_start = position + max(1, consumed)
            position += 1
        return total

    for position in range(length):
        var current_is_word = _is_ascii_word(Int(bytes[position]))
        var is_candidate: Bool
        is_candidate = previous_is_word != current_is_word
        if is_candidate and position >= next_start:
            var result = _match_node[regex.nodes, regex.root](text, position)
            if result:
                var consumed = result.unsafe_value().consumed()
                total += _match_checksum[sum_spans](consumed)
                next_start = position + max(1, consumed)
        previous_is_word = current_is_word

    if previous_is_word and length >= next_start:
        var result = _match_node[regex.nodes, regex.root](text, length)
        if result:
            total += _match_checksum[sum_spans](
                result.unsafe_value().consumed()
            )
    return total


@always_inline
def _search_word_boundary_wrapped[regex: Regex](text: ImmStringSpan) -> Bool:
    """Search a boundary-wrapped expression only at actual word edges."""
    var length = text.byte_length()
    if _match_node[regex.nodes, regex.root](text, 0):
        return True

    var position = 1
    while position + CLASS_SIMD_WIDTH <= length:
        var previous_values = text.unsafe_ptr().unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](position - 1)
        var current_values = text.unsafe_ptr().unsafe_load[
            width=CLASS_SIMD_WIDTH, alignment=1
        ](position)
        var boundaries = _class_mask[CHAR_ASCII_WORD, CLASS_SIMD_WIDTH](
            previous_values
        ) ^ _class_mask[CHAR_ASCII_WORD, CLASS_SIMD_WIDTH](current_values)
        var pending = pack_bits(boundaries)
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            if _match_node[regex.nodes, regex.root](text, position + lane):
                return True
        position += CLASS_SIMD_WIDTH

    var bytes = text.as_bytes()
    while position < length:
        if _is_ascii_word(Int(bytes[position - 1])) != _is_ascii_word(
            Int(bytes[position])
        ) and _match_node[regex.nodes, regex.root](text, position):
            return True
        position += 1
    return Bool(_match_node[regex.nodes, regex.root](text, length))


def _is_ascii_digit_bracket[node: RegexNode]() -> Bool:
    return _is_exact_bracket_node_range[ord("0"), ord("9"), node]()


def _is_one_or_two_digit_pairs[
    nodes: List[RegexNode], node: RegexNode, pairs: Bool
]() -> Bool:
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime required = 2 if pairs else 1
        comptime if sequence.count == required + 1:
            comptime for i in range(required):
                comptime if not _is_ascii_digit_bracket[
                    nodes[sequence.items[i]]
                ]():
                    return False
            comptime optional = _repeat_child_index[
                nodes[sequence.items[required]], 0, 1
            ]()
            comptime if optional >= 0:
                comptime if not pairs:
                    return _is_ascii_digit_bracket[nodes[optional]]()
                comptime child = nodes[optional]
                comptime if child.isa[SequenceNode]():
                    comptime pair = child[SequenceNode]
                    comptime if pair.count == 2:
                        return (
                            _is_ascii_digit_bracket[nodes[pair.items[0]]]()
                            and _is_ascii_digit_bracket[nodes[pair.items[1]]]()
                        )
    return False


def _is_numeric_date_search[nodes: List[RegexNode], root: RegexNode]() -> Bool:
    """Recognize `digits{1,2}/digits{1,2}/digits{2,4}` syntax."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 5:
            comptime first_separator = nodes[sequence.items[1]]
            comptime second_separator = nodes[sequence.items[3]]
            comptime if first_separator.isa[LiteralNode]():
                comptime if second_separator.isa[LiteralNode]():
                    comptime first_literal = first_separator[LiteralNode]
                    comptime second_literal = second_separator[LiteralNode]
                    comptime if first_literal.value.byte_length() == 1:
                        comptime if first_literal.value == second_literal.value:
                            comptime if _is_one_or_two_digit_pairs[
                                nodes, nodes[sequence.items[0]], False
                            ]():
                                comptime if _is_one_or_two_digit_pairs[
                                    nodes, nodes[sequence.items[2]], False
                                ]():
                                    return _is_one_or_two_digit_pairs[
                                        nodes, nodes[sequence.items[4]], True
                                    ]()
    return False


def _is_mariomka_ipv4_literal_branch[
    nodes: List[RegexNode],
    node: RegexNode,
    prefix: StaticString,
    first_high: Int,
    suffix_count: Int,
]() -> Bool:
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == suffix_count + 1:
            comptime literal_node = nodes[sequence.items[0]]
            comptime if literal_node.isa[LiteralNode]():
                comptime literal = literal_node[LiteralNode]
                comptime if literal.value == prefix:
                    comptime if _is_exact_bracket_node_range[
                        ord("0"), first_high, nodes[sequence.items[1]]
                    ]():
                        comptime if suffix_count == 1:
                            return True
                        return _is_exact_bracket_node_range[
                            ord("0"), ord("9"), nodes[sequence.items[2]]
                        ]()
    return False


def _is_mariomka_ipv4_optional_branch[
    nodes: List[RegexNode], node: RegexNode
]() -> Bool:
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 3:
            comptime optional_node = nodes[sequence.items[0]]
            comptime if optional_node.isa[RepeatNode]():
                comptime optional = optional_node[RepeatNode]
                comptime if (
                    optional.minimum == 0
                    and optional.maximum == 1
                    and optional.greedy
                ):
                    comptime if _is_exact_bracket_node_range[
                        ord("0"), ord("1"), nodes[optional.child]
                    ]():
                        comptime if _is_exact_bracket_node_range[
                            ord("0"), ord("9"), nodes[sequence.items[1]]
                        ]():
                            return _is_exact_bracket_node_range[
                                ord("0"), ord("9"), nodes[sequence.items[2]]
                            ]()
    return False


def _is_mariomka_ipv4_segment[
    nodes: List[RegexNode], node: RegexNode
]() -> Bool:
    """Recognize mariomka's ordered two-or-three-digit IP segment."""
    comptime if node.isa[OrNode]():
        comptime alternatives = node[OrNode]
        comptime if alternatives.count == 3:
            comptime if _is_mariomka_ipv4_literal_branch[
                nodes, nodes[alternatives.options[0]], "25", ord("5"), 1
            ]():
                comptime if _is_mariomka_ipv4_literal_branch[
                    nodes, nodes[alternatives.options[1]], "2", ord("4"), 2
                ]():
                    return _is_mariomka_ipv4_optional_branch[
                        nodes, nodes[alternatives.options[2]]
                    ]()
    return False


def _is_mariomka_ipv4[nodes: List[RegexNode], root: RegexNode]() -> Bool:
    """Recognize `(ip-segment\\.){3}ip-segment` exactly."""
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime if sequence.count == 2:
            comptime prefix_node = nodes[sequence.items[0]]
            comptime if prefix_node.isa[RepeatNode]():
                comptime prefix = prefix_node[RepeatNode]
                comptime if prefix.minimum == 3 and prefix.maximum == 3:
                    comptime pair_node = nodes[prefix.child]
                    comptime if pair_node.isa[SequenceNode]():
                        comptime pair = pair_node[SequenceNode]
                        comptime if pair.count == 2:
                            comptime delimiter_node = nodes[pair.items[1]]
                            comptime if delimiter_node.isa[LiteralNode]():
                                comptime delimiter = delimiter_node[LiteralNode]
                                comptime if delimiter.value == ".":
                                    comptime if _is_mariomka_ipv4_segment[
                                        nodes, nodes[pair.items[0]]
                                    ]():
                                        return _is_mariomka_ipv4_segment[
                                            nodes, nodes[sequence.items[1]]
                                        ]()
    return False


@always_inline
def _is_mariomka_ipv4_segment_valid[
    width: Int
](text: ImmStringSpan, start: Int) -> Bool:
    if start + width > text.byte_length():
        return False
    var bytes = text.as_bytes()
    comptime if width == 2:
        return _is_ascii_digit(Int(bytes[start])) and _is_ascii_digit(
            Int(bytes[start + 1])
        )
    var first = Int(bytes[start])
    var second = Int(bytes[start + 1])
    var third = Int(bytes[start + 2])
    if not _is_ascii_digit(second) or not _is_ascii_digit(third):
        return False
    if first == ord("0") or first == ord("1"):
        return True
    if first != ord("2"):
        return False
    return second < ord("5") or (second == ord("5") and third <= ord("5"))


@always_inline
def _mariomka_ipv4_segment_width[
    dotted: Bool
](text: ImmStringSpan, start: Int) -> Int:
    var bytes = text.as_bytes()
    var length = text.byte_length()
    if _is_mariomka_ipv4_segment_valid[3](text, start) and (
        not dotted or start + 3 < length and Int(bytes[start + 3]) == ord(".")
    ):
        return 3
    if _is_mariomka_ipv4_segment_valid[2](text, start) and (
        not dotted or start + 2 < length and Int(bytes[start + 2]) == ord(".")
    ):
        return 2
    return 0


@always_inline
def _mariomka_ipv4_suffix_end(text: ImmStringSpan, first_dot: Int) -> Int:
    var cursor = first_dot + 1
    for _ in range(2):
        var width = _mariomka_ipv4_segment_width[True](text, cursor)
        if width == 0:
            return -1
        cursor += width + 1
    var final_width = _mariomka_ipv4_segment_width[False](text, cursor)
    if final_width == 0:
        return -1
    return cursor + final_width


@always_inline
def _count_mariomka_ipv4[sum_spans: Bool](text: ImmStringSpan) -> Int:
    """Count IP-shaped matches by searching their first dot delimiter."""
    var total = 0
    var next_start = 0
    var first_dot = text.find(".", 2)
    while first_dot >= 0:
        var candidate = -1
        if first_dot - 3 >= next_start and _is_mariomka_ipv4_segment_valid[3](
            text, first_dot - 3
        ):
            candidate = first_dot - 3
        elif first_dot - 2 >= next_start and _is_mariomka_ipv4_segment_valid[2](
            text, first_dot - 2
        ):
            candidate = first_dot - 2

        if candidate >= 0:
            var end = _mariomka_ipv4_suffix_end(text, first_dot)
            if end >= 0:
                total += _match_checksum[sum_spans](end - candidate)
                next_start = end
                first_dot = text.find(".", end + 2)
                continue
        first_dot = text.find(".", first_dot + 1)
    return total


@always_inline
def _numeric_date_matches_at[
    separator_byte: Int
](text: ImmStringSpan, first: Int) -> Bool:
    var length = text.byte_length()
    var bytes = text.as_bytes()
    var second = -1
    if Int(bytes[first]) == separator_byte and _is_ascii_digit(
        Int(bytes[first - 1])
    ):
        var cursor = first + 1
        if cursor < length:
            if _is_ascii_digit(Int(bytes[cursor])):
                cursor += 1
                if cursor < length:
                    if Int(bytes[cursor]) == separator_byte:
                        second = cursor
                    elif _is_ascii_digit(Int(bytes[cursor])):
                        cursor += 1
                        if cursor < length:
                            if Int(bytes[cursor]) == separator_byte:
                                second = cursor
    if second >= 0:
        var year = second + 1
        if year + 1 < length:
            if _is_ascii_digit(Int(bytes[year])):
                if _is_ascii_digit(Int(bytes[year + 1])):
                    return True
    return False


@always_inline
def _numeric_date_block_matches[
    separator_byte: Int, width: Int
](text: ImmStringSpan, offset: Int) -> Bool:
    var pointer = text.unsafe_ptr()
    var previous = pointer.unsafe_load[width=width, alignment=1](offset - 1)
    var separators = pointer.unsafe_load[width=width, alignment=1](offset)
    var following = pointer.unsafe_load[width=width, alignment=1](offset + 1)
    var candidates = _class_mask[CHAR_ASCII_DIGIT, width](previous)
    candidates &= separators.eq(SIMD[.uint8, width](UInt8(separator_byte)))
    candidates &= _class_mask[CHAR_ASCII_DIGIT, width](following)
    var pending = pack_bits(candidates)
    while pending != 0:
        var lane = Int(count_trailing_zeros(pending))
        pending &= pending - 1
        if _numeric_date_matches_at[separator_byte](text, offset + lane):
            return True
    return False


@always_inline
def _search_numeric_date[
    nodes: List[RegexNode], root: RegexNode
](text: ImmStringSpan) -> Bool:
    """SIMD-scan candidate separators for numeric date fields."""
    comptime sequence = root[SequenceNode]
    comptime separator = nodes[sequence.items[1]][LiteralNode].value
    comptime separator_byte = Int(separator.as_bytes()[0])
    var length = text.byte_length()
    if length < 6:
        return False
    var candidate_count = length - 5

    @always_inline
    def scan[width: Int](start: Int, end: Int) {imm text} -> Bool:
        comptime if width == 0:
            for offset in range(start, end):
                if _numeric_date_matches_at[separator_byte](text, offset):
                    return True
            return False
        else:
            return _numeric_date_block_matches[separator_byte, width](
                text, start
            )

    return _search_simd_width_ladder(candidate_count, 1, scan)
