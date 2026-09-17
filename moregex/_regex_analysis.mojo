"""Compile-time regex shape analysis."""

from ._ast import (
    ASSERT_INPUT_END,
    ASSERT_INPUT_START,
    ASSERT_LINE_END,
    ASSERT_LINE_START,
    CHAR_ASCII_DIGIT,
    CHAR_ASCII_WHITESPACE,
    CHAR_BYTE_DOT,
    CHAR_BYTE_DOTALL,
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
from std.algorithm.functional import vectorize
from std.math import iota
from std.sys import CompilationTarget, llvm_intrinsic, simd_width_of
from std.sys.intrinsics import masked_load

from ._regex_common import (
    CLASS_SIMD_WIDTH,
    _accepts_class,
    _bracket_accepts,
    _byte_range_mask,
    _class_mask,
)
from ._regex_semantics import _semantic_fixed_width, _semantic_maximum_width
from ._syntax import Regex


@fieldwise_init
struct _LinePrefixRunLiteralPlan(Copyable):
    var repeat_index: Int
    var literal_index: Int


@fieldwise_init
struct _AnchoredLazyLiteralPlan(Copyable):
    var prefix_repeat_index: Int
    var prefix_literal_index: Int
    var search_literal_index: Int
    var suffix_item: Int


def _anchored_lazy_literal_plan[
    nodes: List[RegexNode], node_index: Int
]() -> Optional[_AnchoredLazyLiteralPlan]:
    """Recognize `^class*LITERAL.*?LITERAL...` on bounded line spans."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count >= 5:
            comptime prefix_node = nodes[sequence.items[1]]
            comptime prefix_literal_node = nodes[sequence.items[2]]
            comptime lazy_node = nodes[sequence.items[3]]
            comptime search_literal_node = nodes[sequence.items[4]]
            comptime if (
                _is_start_assertion_node[nodes, sequence.items[0]]()
                and prefix_node.isa[RepeatNode]()
                and prefix_literal_node.isa[LiteralNode]()
                and lazy_node.isa[RepeatNode]()
                and search_literal_node.isa[LiteralNode]()
            ):
                comptime prefix = prefix_node[RepeatNode]
                comptime prefix_literal = prefix_literal_node[LiteralNode]
                comptime lazy = lazy_node[RepeatNode]
                comptime lazy_child = nodes[lazy.child]
                comptime search_literal = search_literal_node[LiteralNode]
                comptime if (
                    prefix.minimum == 0
                    and prefix.maximum == -1
                    and _is_one_byte_class_node[nodes, prefix.child]()
                    and prefix_literal.value.byte_length() > 0
                    and not _node_start_accepts[nodes, prefix.child](
                        Int(prefix_literal.value.as_bytes()[0])
                    )
                    and lazy.minimum == 0
                    and lazy.maximum == -1
                    and not lazy.greedy
                    and lazy_child.isa[CharClassNode]()
                    and (
                        lazy_child[CharClassNode].kind == CHAR_BYTE_DOT
                        or lazy_child[CharClassNode].kind == CHAR_UNICODE_DOT
                    )
                    and search_literal.value.byte_length() > 0
                ):
                    return _AnchoredLazyLiteralPlan(
                        sequence.items[1],
                        sequence.items[2],
                        sequence.items[4],
                        5,
                    )
    return None


def _line_prefix_run_literal_plan[
    nodes: List[RegexNode], node_index: Int
]() -> Optional[_LinePrefixRunLiteralPlan]:
    """Recognize `^class*LITERAL.*` for line-oriented execution."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 4:
            comptime prefix_node = nodes[sequence.items[1]]
            comptime literal_node = nodes[sequence.items[2]]
            comptime tail_node = nodes[sequence.items[3]]
            comptime if (
                _is_start_assertion_node[nodes, sequence.items[0]]()
                and prefix_node.isa[RepeatNode]()
                and literal_node.isa[LiteralNode]()
                and tail_node.isa[RepeatNode]()
            ):
                comptime prefix = prefix_node[RepeatNode]
                comptime literal = literal_node[LiteralNode]
                comptime tail = tail_node[RepeatNode]
                comptime tail_child = nodes[tail.child]
                comptime if (
                    prefix.minimum == 0
                    and prefix.maximum == -1
                    and literal.value.byte_length() > 0
                    and not _node_start_accepts[nodes, prefix.child](
                        Int(literal.value.as_bytes()[0])
                    )
                    and tail.minimum == 0
                    and tail.maximum == -1
                    and tail_child.isa[CharClassNode]()
                    and (
                        tail_child[CharClassNode].kind == CHAR_BYTE_DOT
                        or tail_child[CharClassNode].kind == CHAR_UNICODE_DOT
                    )
                ):
                    return _LinePrefixRunLiteralPlan(
                        sequence.items[1], sequence.items[2]
                    )
    return None


def _sequence_mandatory_capture_mask[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    comptime if item == sequence.count:
        return 0
    return _mandatory_capture_mask[nodes, sequence.items[item]]() | (
        _sequence_mandatory_capture_mask[nodes, sequence, item + 1]()
    )


def _alternation_mandatory_capture_mask[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    comptime if alternation.count == 0:
        return 0
    var required = _mandatory_capture_mask[nodes, alternation.options[0]]()
    comptime for option in range(1, alternation.count):
        required &= _mandatory_capture_mask[
            nodes, alternation.options[option]
        ]()
    return required


def _mandatory_capture_mask[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return capture groups participating in every match of an AST node."""
    comptime node = nodes[node_index]
    comptime if node.isa[CaptureNode]():
        comptime capture = node[CaptureNode]
        return (Int(1) << (capture.index - 1)) | _mandatory_capture_mask[
            nodes, capture.child
        ]()
    elif node.isa[SequenceNode]():
        return _sequence_mandatory_capture_mask[nodes, node[SequenceNode], 0]()
    elif node.isa[OrNode]():
        return _alternation_mandatory_capture_mask[nodes, node[OrNode]]()
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum > 0:
            return _mandatory_capture_mask[nodes, repeat.child]()
        return 0
    return 0


def _all_captures_mandatory[regex: Regex]() -> Bool:
    """Return whether every numbered group participates in every match."""
    comptime if regex.capture_count == 0:
        return True
    comptime expected = (Int(1) << regex.capture_count) - 1
    return (
        _mandatory_capture_mask[regex.capture_nodes, regex.capture_root]()
        == expected
    )


def _constant_capture_participation_sequence[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    """Return the participating capture count, or -1 when it can vary."""
    comptime if item == sequence.count:
        return 0
    else:
        comptime head = _constant_capture_participation[
            nodes, sequence.items[item]
        ]()
        comptime tail = _constant_capture_participation_sequence[
            nodes, sequence, item + 1
        ]()
        comptime if head < 0 or tail < 0:
            return -1
        return head + tail


def _constant_capture_participation_alternation[
    nodes: List[RegexNode], alternation: OrNode
]() -> Int:
    """Return a common alternative capture count, or -1 when it varies."""
    comptime if alternation.count == 0:
        return 0
    else:
        comptime expected = _constant_capture_participation[
            nodes, alternation.options[0]
        ]()
        comptime if expected < 0:
            return -1
        comptime for option in range(1, alternation.count):
            comptime actual = _constant_capture_participation[
                nodes, alternation.options[option]
            ]()
            comptime if actual != expected:
                return -1
        return expected


def _constant_capture_participation[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Return captures participating in every match, independent of identity.

    A negative result means that the count can vary. A repeated branch with
    captures is conservative: different iterations may populate different
    groups even when each iteration has the same capture count.
    """
    comptime node = nodes[node_index]
    comptime if node.isa[CaptureNode]():
        comptime child = _constant_capture_participation[
            nodes, node[CaptureNode].child
        ]()
        comptime if child < 0:
            return -1
        return child + 1
    elif node.isa[SequenceNode]():
        return _constant_capture_participation_sequence[
            nodes, node[SequenceNode], 0
        ]()
    elif node.isa[OrNode]():
        return _constant_capture_participation_alternation[
            nodes, node[OrNode]
        ]()
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime child = _constant_capture_participation[nodes, repeat.child]()
        comptime if repeat.maximum == 0 or child == 0:
            return 0
        comptime if repeat.minimum == 0 or repeat.maximum != 1 or child < 0:
            return -1
        return child
    return 0


def _constant_capture_count[regex: Regex]() -> Int:
    """Return the fixed participating-group count including group zero."""
    comptime captures = _constant_capture_participation[
        regex.capture_nodes, regex.capture_root
    ]()
    comptime if captures < 0:
        return -1
    return captures + 1


def _all_literal_options[
    nodes: List[RegexNode], alternation: OrNode, minimum: Int = 0
]() -> Bool:
    """Return at compile time whether every alternative is one literal."""
    comptime for i in range(alternation.count):
        comptime option = nodes[alternation.options[i]]
        comptime if not option.isa[LiteralNode]():
            return False
        else:
            comptime if option[LiteralNode].value.byte_length() < minimum:
                return False
    return True


def _literal_alternation_same_first_byte[
    nodes: List[RegexNode], alternation: OrNode
]() -> Bool:
    comptime if alternation.count == 0:
        return False
    comptime first_literal = nodes[alternation.options[0]][LiteralNode]
    comptime if first_literal.value.byte_length() == 0:
        return False
    comptime first = first_literal.value.as_bytes()[0]
    comptime for i in range(1, alternation.count):
        comptime literal = nodes[alternation.options[i]][LiteralNode]
        comptime if (
            literal.value.byte_length() == 0
            or literal.value.as_bytes()[0] != first
        ):
            return False
    return True


@always_inline
def _bracket_mask[
    node: BracketClassNode, width: Int
](values: SIMD[.uint8, width]) -> SIMD[.bool, width]:
    comptime if _is_ascii_fold_pair[node]():
        # ASCII letter case folding is one bit operation plus one comparison;
        # treating the two cases as independent ranges costs four comparisons.
        comptime folded = UInt8(node.lows[0] | 0x20)
        return (values | SIMD[.uint8, width](0x20)).eq(
            SIMD[.uint8, width](folded)
        )
    var accepted = SIMD[.bool, width](fill=False)
    comptime for i in range(node.count):
        accepted |= _byte_range_mask[node.lows[i], node.highs[i], width](values)
    comptime if node.negated:
        return accepted ^ SIMD[.bool, width](fill=True)
    return accepted


def _minimum_alternation_width[
    nodes: List[RegexNode], alternation: OrNode, option: Int
]() -> Int:
    comptime if option == alternation.count:
        return 0
    elif option + 1 == alternation.count:
        return _minimum_node_width[nodes, alternation.options[option]]()
    else:
        return min(
            _minimum_node_width[nodes, alternation.options[option]](),
            _minimum_alternation_width[nodes, alternation, option + 1](),
        )


def _minimum_sequence_width[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    comptime if item == sequence.count:
        return 0
    else:
        return (
            _minimum_node_width[nodes, sequence.items[item]]()
            + _minimum_sequence_width[nodes, sequence, item + 1]()
        )


def _minimum_node_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return the minimum bytes consumed by any successful match."""
    comptime node = nodes[node_index]
    comptime if node.isa[EmptyNode]() or node.isa[ZeroWidthNode]():
        return 0
    elif node.isa[LiteralNode]():
        return node[LiteralNode].value.byte_length()
    elif node.isa[CharClassNode]() or node.isa[BracketClassNode]():
        return 1
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 0:
            return 0
        return _minimum_alternation_width[nodes, alternation, 0]()
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        return repeat.minimum * _minimum_node_width[nodes, repeat.child]()
    else:
        return _minimum_sequence_width[nodes, node[SequenceNode], 0]()


def _maximum_node_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return the maximum bytes consumed, or -1 when unbounded."""
    return comptime (_semantic_maximum_width(nodes, node_index))


def _sequence_required_literal_index[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    comptime if item == sequence.count:
        return -1
    else:
        comptime child = _required_literal_index[nodes, sequence.items[item]]()
        comptime suffix = _sequence_required_literal_index[
            nodes, sequence, item + 1
        ]()
        comptime if child < 0:
            return suffix
        elif suffix < 0:
            return child
        else:
            comptime child_length = nodes[child][
                LiteralNode
            ].value.byte_length()
            comptime suffix_length = nodes[suffix][
                LiteralNode
            ].value.byte_length()
            return child if child_length >= suffix_length else suffix


def _required_literal_index[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return a longest literal required by every match, or `-1`."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return node_index if node[LiteralNode].value.byte_length() > 0 else -1
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum > 0:
            return _required_literal_index[nodes, repeat.child]()
        return -1
    elif node.isa[SequenceNode]():
        return _sequence_required_literal_index[nodes, node[SequenceNode], 0]()
    return -1


def _one_byte_node_coverage[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Count accepted byte values, or return 257 for a non-byte node."""
    comptime node = nodes[node_index]
    comptime if node.isa[CharClassNode]():
        comptime kind = node[CharClassNode].kind
        comptime if kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL:
            return 257
        var coverage = 0
        for value in range(256):
            if _accepts_class[kind](value):
                coverage += 1
        return coverage
    elif node.isa[BracketClassNode]():
        var coverage = 0
        for value in range(256):
            if _bracket_accepts[node[BracketClassNode]](value):
                coverage += 1
        return coverage
    return 257


def _sequence_required_one_byte_node[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int, best: Int
]() -> Int:
    comptime if item == sequence.count:
        return best
    else:
        comptime child = _required_one_byte_node_index[
            nodes, sequence.items[item]
        ]()
        comptime if child >= 0 and (
            best < 0
            or _one_byte_node_coverage[nodes, child]()
            < _one_byte_node_coverage[nodes, best]()
        ):
            return _sequence_required_one_byte_node[
                nodes, sequence, item + 1, child
            ]()
        return _sequence_required_one_byte_node[
            nodes, sequence, item + 1, best
        ]()


def _required_one_byte_node_index[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Return the most selective byte class required by every match."""
    comptime node = nodes[node_index]
    comptime if node.isa[CharClassNode]() or node.isa[BracketClassNode]():
        return (
            node_index if _one_byte_node_coverage[nodes, node_index]()
            <= 256 else -1
        )
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum > 0:
            return _required_one_byte_node_index[nodes, repeat.child]()
        return -1
    elif node.isa[SequenceNode]():
        return _sequence_required_one_byte_node[
            nodes, node[SequenceNode], 0, -1
        ]()
    return -1


@always_inline
def _sequence_start_accepts[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
](value: Int) -> Bool:
    comptime if item == sequence.count:
        return False
    else:
        comptime child = sequence.items[item]
        if _node_start_accepts[nodes, child](value):
            return True
        comptime if _minimum_node_width[nodes, child]() == 0:
            return _sequence_start_accepts[nodes, sequence, item + 1](value)
        return False


@always_inline
def _node_start_accepts[
    nodes: List[RegexNode], node_index: Int
](value: Int) -> Bool:
    """Return whether `value` can begin a non-empty match of a node."""
    comptime node = nodes[node_index]
    comptime if node.isa[EmptyNode]() or node.isa[ZeroWidthNode]():
        return False
    elif node.isa[LiteralNode]():
        comptime literal = node[LiteralNode]
        comptime if literal.value.byte_length() == 0:
            return False
        return value == Int(literal.value.as_bytes()[0])
    elif node.isa[CharClassNode]():
        return _accepts_class[node[CharClassNode].kind](value)
    elif node.isa[BracketClassNode]():
        return _bracket_accepts[node[BracketClassNode]](value)
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime for i in range(alternation.count):
            if _node_start_accepts[nodes, alternation.options[i]](value):
                return True
        return False
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.maximum == 0:
            return False
        return _node_start_accepts[nodes, repeat.child](value)
    else:
        return _sequence_start_accepts[nodes, node[SequenceNode], 0](value)


@always_inline
def _sequence_start_mask[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int, width: Int
](values: SIMD[.uint8, width]) -> SIMD[.bool, width]:
    comptime if item == sequence.count:
        return SIMD[.bool, width](fill=False)
    else:
        comptime child = sequence.items[item]
        var accepted = _node_start_mask[nodes, child, width](values)
        comptime if _minimum_node_width[nodes, child]() == 0:
            accepted |= _sequence_start_mask[nodes, sequence, item + 1, width](
                values
            )
        return accepted


@always_inline
def _node_start_mask[
    nodes: List[RegexNode], node_index: Int, width: Int
](values: SIMD[.uint8, width]) -> SIMD[.bool, width]:
    """Vector form of `_node_start_accepts` for candidate discovery."""
    comptime node = nodes[node_index]
    comptime if node.isa[EmptyNode]() or node.isa[ZeroWidthNode]():
        return SIMD[.bool, width](fill=False)
    elif node.isa[LiteralNode]():
        comptime literal = node[LiteralNode]
        comptime if literal.value.byte_length() == 0:
            return SIMD[.bool, width](fill=False)
        return values.eq(SIMD[.uint8, width](literal.value.as_bytes()[0]))
    elif node.isa[CharClassNode]():
        return _class_mask[node[CharClassNode].kind, width](values)
    elif node.isa[BracketClassNode]():
        return _bracket_mask[node[BracketClassNode], width](values)
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        var accepted = SIMD[.bool, width](fill=False)
        comptime for i in range(alternation.count):
            accepted |= _node_start_mask[nodes, alternation.options[i], width](
                values
            )
        return accepted
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.maximum == 0:
            return SIMD[.bool, width](fill=False)
        return _node_start_mask[nodes, repeat.child, width](values)
    else:
        return _sequence_start_mask[nodes, node[SequenceNode], 0, width](values)


def _bracket_coverage_upper_bound[node: BracketClassNode]() -> Int:
    var coverage = 0
    comptime for item in range(node.count):
        coverage += node.highs[item] - node.lows[item] + 1
    return coverage


def _start_filter_is_selective[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Conservatively select roots worth SIMD filtering before matching."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return node[LiteralNode].value.byte_length() > 0
    elif node.isa[CharClassNode]():
        comptime kind = node[CharClassNode].kind
        return kind == CHAR_ASCII_DIGIT or kind == CHAR_ASCII_WHITESPACE
    elif node.isa[BracketClassNode]():
        comptime bracket = node[BracketClassNode]
        comptime coverage = min(256, _bracket_coverage_upper_bound[bracket]())
        comptime if bracket.negated:
            return 256 - coverage <= 32
        return coverage <= 32
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for i in range(alternation.count):
            comptime if not _start_filter_is_selective[
                nodes, alternation.options[i]
            ]():
                return False
        return True
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        return (
            repeat.minimum > 0
            and _start_filter_is_selective[nodes, repeat.child]()
        )
    elif node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 0:
            return False
        comptime first = sequence.items[0]
        comptime if _minimum_node_width[nodes, first]() == 0:
            return False
        return _start_filter_is_selective[nodes, first]()
    return False


def _sequence_has_generic_backtracking_risk[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Bool:
    comptime if item == sequence.count:
        return False
    else:
        comptime child_index = sequence.items[item]
        comptime child = nodes[child_index]
        comptime if item + 1 < sequence.count and child.isa[RepeatNode]():
            comptime repeat = child[RepeatNode]
            comptime if repeat.maximum < 0 or repeat.maximum != repeat.minimum:
                return True
        comptime if _has_generic_backtracking_risk[nodes, child_index]():
            return True
        return _sequence_has_generic_backtracking_risk[
            nodes, sequence, item + 1
        ]()


def _has_generic_backtracking_risk[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Identify fallback shapes that can retry a variable repeat per start."""
    comptime node = nodes[node_index]
    comptime if node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime for i in range(alternation.count):
            comptime if _has_generic_backtracking_risk[
                nodes, alternation.options[i]
            ]():
                return True
        return False
    elif node.isa[RepeatNode]():
        return _has_generic_backtracking_risk[nodes, node[RepeatNode].child]()
    elif node.isa[SequenceNode]():
        return _sequence_has_generic_backtracking_risk[
            nodes, node[SequenceNode], 0
        ]()
    return False


def _fixed_node_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return a node's exact byte width, or -1 when it is variable."""
    return comptime (_semantic_fixed_width(nodes, node_index, False))


def _is_ascii_fold_pair[node: BracketClassNode]() -> Bool:
    """Return whether a bracket is exactly one ASCII letter in both cases."""
    comptime if node.negated or node.count != 2:
        return False
    comptime if node.lows[0] != node.highs[0] or node.lows[1] != node.highs[1]:
        return False
    return (
        node.lows[0] + 32 == node.lows[1] or node.lows[1] + 32 == node.lows[0]
    )


def _is_ascii_letters[node: BracketClassNode]() -> Bool:
    """Return whether a bracket is exactly `[A-Za-z]`."""
    comptime if node.negated or node.count != 2:
        return False
    return (
        node.lows[0] == ord("A")
        and node.highs[0] == ord("Z")
        and node.lows[1] == ord("a")
        and node.highs[1] == ord("z")
    ) or (
        node.lows[1] == ord("A")
        and node.highs[1] == ord("Z")
        and node.lows[0] == ord("a")
        and node.highs[0] == ord("z")
    )


def _is_ascii_fold_pair_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[BracketClassNode]():
        return _is_ascii_fold_pair[node[BracketClassNode]]()
    return False


def _all_casefold_prefixed_sequence_options[
    nodes: List[RegexNode], alternation: OrNode
]() -> Bool:
    comptime for i in range(alternation.count):
        comptime node = nodes[alternation.options[i]]
        comptime if not node.isa[SequenceNode]():
            return False
        else:
            comptime sequence = node[SequenceNode]
            comptime if sequence.count < 3:
                return False
            elif (
                not _is_ascii_fold_pair_node[nodes, sequence.items[0]]()
                or not _is_ascii_fold_pair_node[nodes, sequence.items[1]]()
                or not _is_ascii_fold_pair_node[nodes, sequence.items[2]]()
            ):
                return False
    return alternation.count > 0


def _sequence_prefix_literal_index[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Return a non-empty literal prefix node, or -1 when none exists."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count > 0:
            comptime prefix_index = sequence.items[0]
            comptime prefix = nodes[prefix_index]
            comptime if prefix.isa[LiteralNode]():
                comptime if prefix[LiteralNode].value.byte_length() > 0:
                    return prefix_index
    return -1


def _all_prefixed_sequence_options[
    nodes: List[RegexNode], alternation: OrNode, minimum: Int = 1
]() -> Bool:
    comptime for i in range(alternation.count):
        comptime prefix_index = _sequence_prefix_literal_index[
            nodes, alternation.options[i]
        ]()
        comptime if prefix_index < 0:
            return False
        else:
            comptime prefix = nodes[prefix_index][LiteralNode]
            comptime if prefix.value.byte_length() < minimum:
                return False
    return alternation.count > 0


def _is_bounded_line_gap_option[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `literal(?:\\s*.+\\s*){0,n}literal`."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count != 3:
            return False
        comptime prefix = nodes[sequence.items[0]]
        comptime gap_node = nodes[sequence.items[1]]
        comptime suffix = nodes[sequence.items[2]]
        comptime if (
            not prefix.isa[LiteralNode]()
            or prefix[LiteralNode].value.byte_length() == 0
            or not suffix.isa[LiteralNode]()
            or suffix[LiteralNode].value.byte_length() == 0
        ):
            return False
        comptime if gap_node.isa[RepeatNode]():
            comptime gap = gap_node[RepeatNode]
            comptime if (
                gap.minimum != 0 or gap.maximum <= 0 or not gap.greedy
            ):
                return False
            comptime child = nodes[gap.child]
            comptime if child.isa[SequenceNode]():
                comptime middle = child[SequenceNode]
                comptime if middle.count != 3:
                    return False
                comptime leading_node = nodes[middle.items[0]]
                comptime dot_node = nodes[middle.items[1]]
                comptime trailing_node = nodes[middle.items[2]]
                comptime if (
                    not leading_node.isa[RepeatNode]()
                    or not dot_node.isa[RepeatNode]()
                    or not trailing_node.isa[RepeatNode]()
                ):
                    return False
                comptime leading = leading_node[RepeatNode]
                comptime dot = dot_node[RepeatNode]
                comptime trailing = trailing_node[RepeatNode]
                comptime if (
                    leading.minimum != 0
                    or leading.maximum != -1
                    or not leading.greedy
                    or dot.minimum != 1
                    or dot.maximum != -1
                    or not dot.greedy
                    or trailing.minimum != 0
                    or trailing.maximum != -1
                    or not trailing.greedy
                ):
                    return False
                comptime leading_child = nodes[leading.child]
                comptime dot_child = nodes[dot.child]
                comptime trailing_child = nodes[trailing.child]
                return (
                    leading_child.isa[CharClassNode]()
                    and leading_child[CharClassNode].kind
                    == CHAR_ASCII_WHITESPACE
                    and dot_child.isa[CharClassNode]()
                    and dot_child[CharClassNode].kind == CHAR_BYTE_DOT
                    and trailing_child.isa[CharClassNode]()
                    and trailing_child[CharClassNode].kind
                    == CHAR_ASCII_WHITESPACE
                )
            return False
        return False
    return False


def _is_bounded_line_gap_literal_alternation[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 0:
            return False
        comptime for option in range(alternation.count):
            comptime if not _is_bounded_line_gap_option[
                nodes, alternation.options[option]
            ]():
                return False
        return True
    return False


def _multiline_literal_edge_index[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Return the shared literal in `(?m)^literal|literal$`, or -1."""
    comptime node = nodes[node_index]
    comptime if node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 2:
            comptime first_node = nodes[alternation.options[0]]
            comptime second_node = nodes[alternation.options[1]]
            comptime if (
                first_node.isa[SequenceNode]()
                and second_node.isa[SequenceNode]()
            ):
                comptime first = first_node[SequenceNode]
                comptime second = second_node[SequenceNode]
                comptime if second.count == 2:
                    comptime second_literal = nodes[second.items[0]]
                    comptime second_anchor = nodes[second.items[1]]
                    comptime if (
                        second_literal.isa[LiteralNode]()
                        and second_anchor.isa[ZeroWidthNode]()
                    ):
                        comptime if (
                            second_anchor[ZeroWidthNode].kind != ASSERT_LINE_END
                        ):
                            return -1
                        comptime if first.count == 2:
                            comptime first_anchor = nodes[first.items[0]]
                            comptime first_literal = nodes[first.items[1]]
                            comptime if (
                                first_anchor.isa[ZeroWidthNode]()
                                and first_literal.isa[LiteralNode]()
                            ):
                                comptime if (
                                    first_anchor[ZeroWidthNode].kind
                                    == ASSERT_LINE_START
                                    and first_literal[LiteralNode].value
                                    == second_literal[LiteralNode].value
                                    and first_literal[
                                        LiteralNode
                                    ].value.byte_length()
                                    > 0
                                ):
                                    return first.items[1]
                        comptime if first.count == 3:
                            comptime empty = nodes[first.items[0]]
                            comptime first_anchor = nodes[first.items[1]]
                            comptime first_literal = nodes[first.items[2]]
                            comptime if (
                                empty.isa[EmptyNode]()
                                and first_anchor.isa[ZeroWidthNode]()
                                and first_literal.isa[LiteralNode]()
                            ):
                                comptime if (
                                    first_anchor[ZeroWidthNode].kind
                                    == ASSERT_LINE_START
                                    and first_literal[LiteralNode].value
                                    == second_literal[LiteralNode].value
                                    and first_literal[
                                        LiteralNode
                                    ].value.byte_length()
                                    > 0
                                ):
                                    return first.items[2]
    return -1


def _is_multiline_literal_edge_alternation[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    return _multiline_literal_edge_index[nodes, node_index]() >= 0


def _is_bounded_prefix_literal_alternation[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `one-byte-class{m,n} (literal|...)`."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 2:
            comptime prefix = nodes[sequence.items[0]]
            comptime suffix = nodes[sequence.items[1]]
            comptime if prefix.isa[RepeatNode]() and suffix.isa[OrNode]():
                comptime repeat = prefix[RepeatNode]
                return (
                    repeat.maximum >= 0
                    and _is_one_byte_class_node[nodes, repeat.child]()
                    and _all_literal_options[nodes, suffix[OrNode]]()
                )
    return False


def _is_class_literal_alternation_with_suffix[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `([class]literal|...) [class]`."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 2:
            comptime prefix = nodes[sequence.items[0]]
            comptime if prefix.isa[OrNode]():
                comptime alternation = prefix[OrNode]
                comptime for i in range(alternation.count):
                    comptime option = nodes[alternation.options[i]]
                    comptime if not option.isa[SequenceNode]():
                        return False
                    else:
                        comptime option_sequence = option[SequenceNode]
                        comptime if option_sequence.count != 2:
                            return False
                        else:
                            comptime literal = nodes[option_sequence.items[1]]
                            comptime if (
                                not _is_one_byte_class_node[
                                    nodes, option_sequence.items[0]
                                ]()
                                or not literal.isa[LiteralNode]()
                                or literal[LiteralNode].value.byte_length() == 0
                            ):
                                return False
                return (
                    alternation.count > 0
                    and _is_one_byte_class_node[nodes, sequence.items[1]]()
                )
    return False


def _is_one_byte_class_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[CharClassNode]():
        return (
            node[CharClassNode].kind < CHAR_UNICODE_DOT
            or node[CharClassNode].kind > CHAR_UNICODE_DOTALL
        )
    return node.isa[BracketClassNode]()


def _same_bracket_ranges[
    left: BracketClassNode, right: BracketClassNode
]() -> Bool:
    comptime if left.count != right.count:
        return False
    comptime for i in range(left.count):
        comptime if (
            left.lows[i] != right.lows[i] or left.highs[i] != right.highs[i]
        ):
            return False
    return True


def _nodes_are_disjoint[
    nodes: List[RegexNode], left_index: Int, right_index: Int
]() -> Bool:
    comptime for value in range(256):
        comptime if _one_byte_atom_accepts[nodes, left_index](value):
            comptime if _one_byte_atom_accepts[nodes, right_index](value):
                return False
    return True


def _is_symmetric_bounded_delimited_sequence[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `D [^D]{m,n} C D` where `C` and `D` are disjoint."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 4:
            comptime prefix_node = nodes[sequence.items[0]]
            comptime repeat_node = nodes[sequence.items[1]]
            comptime suffix_node = nodes[sequence.items[3]]
            comptime if (
                prefix_node.isa[BracketClassNode]()
                and repeat_node.isa[RepeatNode]()
                and suffix_node.isa[BracketClassNode]()
            ):
                comptime prefix = prefix_node[BracketClassNode]
                comptime repeat = repeat_node[RepeatNode]
                comptime repeat_child_node = nodes[repeat.child]
                comptime suffix = suffix_node[BracketClassNode]
                comptime if repeat_child_node.isa[BracketClassNode]():
                    comptime repeat_child = repeat_child_node[BracketClassNode]
                    return (
                        not prefix.negated
                        and repeat_child.negated
                        and not suffix.negated
                        and repeat.maximum >= 0
                        and _same_bracket_ranges[prefix, repeat_child]()
                        and _same_bracket_ranges[prefix, suffix]()
                        and _is_one_byte_class_node[nodes, sequence.items[2]]()
                        and _nodes_are_disjoint[
                            nodes, sequence.items[0], sequence.items[2]
                        ]()
                    )
    return False


def _is_exact_bracket_range[
    node: BracketClassNode
](low: Int, high: Int) -> Bool:
    return Bool(
        not node.negated
        and node.count == 1
        and node.lows[0] == low
        and node.highs[0] == high
    )


def _is_exact_bracket_node_range[
    low: Int, high: Int, node: RegexNode
]() -> Bool:
    comptime if node.isa[BracketClassNode]():
        return _is_exact_bracket_range[node[BracketClassNode]](low, high)
    return False


def _is_bounded_capitalized_word_sequence[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `(?:[A-Z][a-z]+\\s*){m,n}`."""
    comptime node = nodes[node_index]
    comptime if node.isa[RepeatNode]():
        comptime outer = node[RepeatNode]
        comptime child_node = nodes[outer.child]
        comptime if (
            outer.minimum > 0
            and outer.maximum >= outer.minimum
            and outer.greedy
            and child_node.isa[SequenceNode]()
        ):
            comptime child = child_node[SequenceNode]
            comptime if child.count == 3:
                comptime uppercase_node = nodes[child.items[0]]
                comptime lowercase_repeat_node = nodes[child.items[1]]
                comptime whitespace_repeat_node = nodes[child.items[2]]
                comptime if (
                    uppercase_node.isa[BracketClassNode]()
                    and lowercase_repeat_node.isa[RepeatNode]()
                    and whitespace_repeat_node.isa[RepeatNode]()
                ):
                    comptime uppercase = uppercase_node[BracketClassNode]
                    comptime lowercase_repeat = lowercase_repeat_node[
                        RepeatNode
                    ]
                    comptime whitespace_repeat = whitespace_repeat_node[
                        RepeatNode
                    ]
                    comptime lowercase_node = nodes[lowercase_repeat.child]
                    comptime whitespace_node = nodes[whitespace_repeat.child]
                    comptime if (
                        lowercase_node.isa[BracketClassNode]()
                        and whitespace_node.isa[CharClassNode]()
                    ):
                        return Bool(
                            _is_exact_bracket_range[uppercase](
                                ord("A"), ord("Z")
                            )
                            and _is_exact_bracket_range[
                                lowercase_node[BracketClassNode]
                            ](ord("a"), ord("z"))
                            and lowercase_repeat.minimum == 1
                            and lowercase_repeat.maximum == -1
                            and lowercase_repeat.greedy
                            and whitespace_repeat.minimum == 0
                            and whitespace_repeat.maximum == -1
                            and whitespace_repeat.greedy
                            and whitespace_node[CharClassNode].kind
                            == CHAR_ASCII_WHITESPACE
                        )
    return False


def _is_nested_run_then_disjoint_class[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `(byte_atom+)*class` with disjoint byte predicates."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 2:
            comptime outer_node = nodes[sequence.items[0]]
            comptime if outer_node.isa[RepeatNode]():
                comptime outer = outer_node[RepeatNode]
                comptime inner_node = nodes[outer.child]
                comptime if inner_node.isa[RepeatNode]():
                    comptime inner = inner_node[RepeatNode]
                    comptime if not (
                        outer.minimum == 0
                        and outer.maximum == -1
                        and outer.greedy
                        and inner.minimum == 1
                        and inner.maximum == -1
                        and inner.greedy
                        and _is_one_byte_class_node[nodes, sequence.items[1]]()
                    ):
                        return False
                    comptime atom = nodes[inner.child]
                    comptime if atom.isa[LiteralNode]():
                        comptime literal = atom[LiteralNode]
                        comptime if literal.value.byte_length() == 1:
                            return not _one_byte_atom_accepts[
                                nodes, sequence.items[1]
                            ](Int(literal.value.as_bytes()[0]))
                        return False
                    comptime if _is_one_byte_class_node[nodes, inner.child]():
                        return _nodes_are_disjoint[
                            nodes, inner.child, sequence.items[1]
                        ]()
    return False


def _is_end_assertion_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[ZeroWidthNode]():
        return node[ZeroWidthNode].kind == ASSERT_INPUT_END
    return False


def _is_start_assertion_node[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[ZeroWidthNode]():
        return node[ZeroWidthNode].kind == ASSERT_INPUT_START
    return False


def _is_start_anchored[nodes: List[RegexNode], node_index: Int]() -> Bool:
    """Return whether the expression can only match at byte zero."""
    comptime node = nodes[node_index]
    comptime if _is_start_assertion_node[nodes, node_index]():
        return True
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime for i in range(sequence.count):
            comptime item = nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]():
                continue
            comptime if item.isa[ZeroWidthNode]():
                comptime if _is_start_assertion_node[
                    nodes, sequence.items[i]
                ]():
                    return True
                continue
            return False
    return False


def _is_end_anchored[nodes: List[RegexNode], node_index: Int]() -> Bool:
    """Return whether the expression requires input end (or its final LF)."""
    comptime node = nodes[node_index]
    comptime if _is_end_assertion_node[nodes, node_index]():
        return True
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime for offset in range(sequence.count):
            comptime i = sequence.count - offset - 1
            comptime item = nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]():
                continue
            comptime if item.isa[ZeroWidthNode]():
                comptime if _is_end_assertion_node[nodes, sequence.items[i]]():
                    return True
                continue
            return False
    return False


def _fixed_sequence_prefix_width[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int
]() -> Int:
    comptime if item == sequence.count - 1:
        return 0
    else:
        comptime width = _fixed_node_width[nodes, sequence.items[item]]()
        comptime suffix_width = _fixed_sequence_prefix_width[
            nodes, sequence, item + 1
        ]()
        comptime if width < 0 or suffix_width < 0:
            return -1
        return width + suffix_width


def _end_anchored_fixed_width[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return consuming width for `fixed-width $`, or -1."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count >= 2:
            comptime if _is_end_assertion_node[
                nodes, sequence.items[sequence.count - 1]
            ]():
                return _fixed_sequence_prefix_width[nodes, sequence, 0]()
    return -1


def _simple_infix_literal_item_from[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int, found: Int
]() -> Int:
    comptime if item == sequence.count:
        return found
    else:
        comptime node_index = sequence.items[item]
        comptime node = nodes[node_index]
        comptime if node.isa[LiteralNode]():
            comptime if node[LiteralNode].value.byte_length() == 0:
                return -1
            comptime if found < 0 or (
                node[LiteralNode].value.byte_length()
                > nodes[sequence.items[found]][LiteralNode].value.byte_length()
            ):
                return _simple_infix_literal_item_from[
                    nodes, sequence, item + 1, item
                ]()
            return _simple_infix_literal_item_from[
                nodes, sequence, item + 1, found
            ]()
        elif node.isa[RepeatNode]():
            comptime if not _is_one_byte_class_node[
                nodes, node[RepeatNode].child
            ]():
                return -1
            comptime repeat_child = nodes[node[RepeatNode].child]
            comptime if repeat_child.isa[CharClassNode]():
                comptime if repeat_child[CharClassNode].kind == CHAR_BYTE_DOT:
                    return -1
        elif not (
            node.isa[EmptyNode]()
            or node.isa[ZeroWidthNode]()
            or _is_one_byte_class_node[nodes, node_index]()
        ):
            return -1
        return _simple_infix_literal_item_from[
            nodes, sequence, item + 1, found
        ]()


def _simple_infix_literal_item_for_root[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime item = _simple_infix_literal_item_from[
            nodes, sequence, 0, -1
        ]()
        comptime if item < 0:
            return -1
        # If a greedy prefix accepts the literal's first byte and nothing
        # follows the literal, the regex must choose the last viable literal
        # in that run. A first-candidate prefilter would change the span.
        comptime if item == sequence.count - 1 and item > 0:
            comptime previous = nodes[sequence.items[item - 1]]
            comptime if previous.isa[RepeatNode]():
                comptime repeat = previous[RepeatNode]
                comptime literal = nodes[sequence.items[item]][LiteralNode]
                comptime first = Int(literal.value.as_bytes()[0])
                comptime if _one_byte_atom_accepts[nodes, repeat.child](first):
                    return -1
        return item
    return -1


def _simple_class_anchor_item_from[
    nodes: List[RegexNode], sequence: SequenceNode, item: Int, best: Int
]() -> Int:
    comptime if item == sequence.count:
        return best
    else:
        comptime node_index = sequence.items[item]
        comptime node = nodes[node_index]
        comptime if _is_one_byte_class_node[nodes, node_index]():
            comptime if best < 0 or (
                _one_byte_node_coverage[nodes, node_index]()
                < _one_byte_node_coverage[nodes, sequence.items[best]]()
            ):
                return _simple_class_anchor_item_from[
                    nodes, sequence, item + 1, item
                ]()
        elif node.isa[RepeatNode]():
            comptime if not _is_one_byte_class_node[
                nodes, node[RepeatNode].child
            ]():
                return -1
        elif node.isa[LiteralNode]():
            comptime if node[LiteralNode].value.byte_length() == 0:
                return -1
        elif not (node.isa[EmptyNode]() or node.isa[ZeroWidthNode]()):
            return -1
        return _simple_class_anchor_item_from[nodes, sequence, item + 1, best]()


def _simple_class_anchor_item_for_root[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Select a required direct byte class in a simple byte sequence."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        return _simple_class_anchor_item_from[
            nodes, node[SequenceNode], 0, -1
        ]()
    return -1


def _leading_repeat_literal_item[
    nodes: List[RegexNode], node_index: Int, require_disjoint: Bool = True
]() -> Int:
    """Return the mandatory literal after a leading one-byte repeat."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count >= 2:
            comptime repeat_node = nodes[sequence.items[0]]
            comptime literal_node = nodes[sequence.items[1]]
            comptime if (
                repeat_node.isa[RepeatNode]()
                and literal_node.isa[LiteralNode]()
            ):
                comptime repeat = repeat_node[RepeatNode]
                comptime literal = literal_node[LiteralNode]
                comptime if (
                    repeat.minimum > 0
                    and _is_one_byte_class_node[nodes, repeat.child]()
                    and literal.value.byte_length() > 0
                    and (
                        not require_disjoint
                        or not _literal_bytes_all_accepted_by_node[
                            nodes, repeat.child, literal.value, 0
                        ]()
                    )
                ):
                    return 1
    return -1


def _literal_bytes_all_accepted_by_node[
    nodes: List[RegexNode], node_index: Int, literal: String, position: Int
]() -> Bool:
    """Return whether every literal byte belongs to one byte predicate."""
    comptime if position == literal.byte_length():
        return True
    else:
        comptime if not _one_byte_atom_accepts[nodes, node_index](
            Int(literal.as_bytes()[position])
        ):
            return False
        return _literal_bytes_all_accepted_by_node[
            nodes, node_index, literal, position + 1
        ]()


def _is_reverse_suffix_class_sequence[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `one-byte literal class* one-byte` sequences."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 4:
            comptime middle = nodes[sequence.items[2]]
            comptime literal = nodes[sequence.items[1]]
            comptime if middle.isa[RepeatNode]() and literal.isa[LiteralNode]():
                comptime repeat = middle[RepeatNode]
                return (
                    repeat.maximum == -1
                    and _is_one_byte_class_node[nodes, sequence.items[0]]()
                    and _is_one_byte_class_node[nodes, repeat.child]()
                    and _is_one_byte_class_node[nodes, sequence.items[3]]()
                    and literal[LiteralNode].value.byte_length() > 0
                )
    return False


def _unbounded_char_repeat_kind[
    nodes: List[RegexNode], node_index: Int, minimum: Int
]() -> Int:
    """Return the repeated character-class kind, or -1."""
    comptime node = nodes[node_index]
    comptime if node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime if repeat.minimum == minimum and repeat.maximum == -1:
            comptime child = nodes[repeat.child]
            comptime if child.isa[CharClassNode]():
                return child[CharClassNode].kind
    return -1


def _is_zero_or_more_dot[nodes: List[RegexNode], node_index: Int]() -> Bool:
    return _unbounded_char_repeat_kind[nodes, node_index, 0]() == CHAR_BYTE_DOT


def _is_zero_or_more_dotall[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime kind = _unbounded_char_repeat_kind[nodes, node_index, 0]()
    return kind == CHAR_BYTE_DOTALL or kind == CHAR_UNICODE_DOTALL


def _is_whole_input_dotall_star[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize a bare `(?s).*`, allowing an inline-flag empty node."""
    comptime if _is_zero_or_more_dotall[nodes, node_index]():
        return True
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 2:
            comptime if nodes[sequence.items[0]].isa[EmptyNode]():
                return _is_zero_or_more_dotall[nodes, sequence.items[1]]()
    return False


def _unicode_dot_kind[nodes: List[RegexNode], node_index: Int]() -> Int:
    """Return the Unicode dot class kind, or -1 for any other atom."""
    comptime node = nodes[node_index]
    comptime if node.isa[CharClassNode]():
        comptime kind = node[CharClassNode].kind
        comptime if kind == CHAR_UNICODE_DOT or kind == CHAR_UNICODE_DOTALL:
            return kind
        return -1
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 2:
            comptime if nodes[sequence.items[0]].isa[EmptyNode]():
                return _unicode_dot_kind[nodes, sequence.items[1]]()
    return -1


def _is_unicode_dotall_plus[nodes: List[RegexNode], node_index: Int]() -> Bool:
    comptime node = nodes[node_index]
    comptime kind = _unbounded_char_repeat_kind[nodes, node_index, 1]()
    comptime if kind >= 0:
        return kind == CHAR_UNICODE_DOTALL
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 2:
            comptime if nodes[sequence.items[0]].isa[EmptyNode]():
                return _is_unicode_dotall_plus[nodes, sequence.items[1]]()
    return False


@always_inline
def _count_unicode_dot[
    exclude_newline: Bool, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count Unicode dot matches or spans with native-width SIMD blocks."""
    var length = text.byte_length()
    var pointer = text.unsafe_ptr()
    var total = 0

    def count_block[width: Int](offset: Int, evl: Int) {mut}:
        var lanes = iota[DType.uint8, width]()
        var active = lanes.lt(SIMD[.uint8, width](UInt8(evl)))
        var values: SIMD[.uint8, width]
        if evl == width:
            values = pointer.unsafe_load[width=width, alignment=1](offset)
        else:
            values = masked_load[width](
                pointer.unsafe_offset(offset),
                active,
                SIMD[.uint8, width](0),
            )
        comptime if sum_spans:
            comptime if exclude_newline:
                var newlines = (
                    values.eq(SIMD[.uint8, width](UInt8(ord("\n")))) & active
                )
                total += evl - newlines.reduce_bit_count()
            else:
                total += evl
        else:
            var continuation = (values & SIMD[.uint8, width](0xC0)).eq(
                SIMD[.uint8, width](0x80)
            )
            var leading = (
                continuation ^ SIMD[.bool, width](fill=True)
            ) & active
            comptime if exclude_newline:
                leading &= values.ne(SIMD[.uint8, width](UInt8(ord("\n"))))
            total += leading.reduce_bit_count()

    vectorize[CLASS_SIMD_WIDTH, unroll_factor=2](length, count_block)
    return total


def _is_multiline_whole_line_sequence[
    nodes: List[RegexNode], sequence: SequenceNode, offset: Int
]() -> Bool:
    comptime start = nodes[sequence.items[offset]]
    comptime repeat_node = nodes[sequence.items[offset + 1]]
    comptime end = nodes[sequence.items[offset + 2]]
    comptime if (
        start.isa[ZeroWidthNode]()
        and repeat_node.isa[RepeatNode]()
        and end.isa[ZeroWidthNode]()
    ):
        comptime repeat = repeat_node[RepeatNode]
        comptime child = nodes[repeat.child]
        comptime if child.isa[CharClassNode]():
            return Bool(
                start[ZeroWidthNode].kind == ASSERT_LINE_START
                and repeat.minimum == 0
                and repeat.maximum == -1
                and child[CharClassNode].kind == CHAR_BYTE_DOT
                and end[ZeroWidthNode].kind == ASSERT_LINE_END
            )
    return False


def _is_multiline_whole_line[nodes: List[RegexNode], node_index: Int]() -> Bool:
    """Recognize `(?m)^.*$`, whose search result is always true."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 3:
            return _is_multiline_whole_line_sequence[nodes, sequence, 0]()
        comptime if sequence.count == 4:
            comptime if nodes[sequence.items[0]].isa[EmptyNode]():
                return _is_multiline_whole_line_sequence[nodes, sequence, 1]()
    return False


def _is_anchored_prefix_delimited_line_at[
    nodes: List[RegexNode], node_index: Int, offset: Int
]() -> Bool:
    comptime sequence = nodes[node_index][SequenceNode]
    comptime start = nodes[sequence.items[0]]
    comptime prefix_node = nodes[sequence.items[1 + offset]]
    comptime body_node = nodes[sequence.items[3 + offset]]
    comptime end = nodes[sequence.items[5 + offset]]
    comptime if (
        not start.isa[ZeroWidthNode]()
        or start[ZeroWidthNode].kind != ASSERT_INPUT_START
        or not prefix_node.isa[RepeatNode]()
        or not body_node.isa[RepeatNode]()
        or not end.isa[ZeroWidthNode]()
        or end[ZeroWidthNode].kind != ASSERT_INPUT_END
    ):
        return False
    else:
        comptime prefix = prefix_node[RepeatNode]
        comptime body = body_node[RepeatNode]
        comptime body_child = nodes[body.child]
        return (
            prefix.minimum == 0
            and prefix.maximum < 0
            and prefix.greedy
            and _is_one_byte_class_node[nodes, prefix.child]()
            and _is_one_byte_class_node[nodes, sequence.items[2 + offset]]()
            and _is_one_byte_class_node[nodes, sequence.items[4 + offset]]()
            and _nodes_are_disjoint[
                nodes, prefix.child, sequence.items[2 + offset]
            ]()
            and body.minimum == 0
            and body.maximum < 0
            and body.greedy
            and body_child.isa[CharClassNode]()
            and (
                body_child[CharClassNode].kind == CHAR_BYTE_DOT
                or body_child[CharClassNode].kind == CHAR_UNICODE_DOT
            )
        )


def _anchored_prefix_delimited_line_offset[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    comptime node = nodes[node_index]
    comptime if not node.isa[SequenceNode]():
        return -1
    else:
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 6:
            return 0 if _is_anchored_prefix_delimited_line_at[
                nodes, node_index, 0
            ]() else -1
        elif (
            sequence.count == 7 and nodes[sequence.items[1]].isa[EmptyNode]()
        ):
            return 1 if _is_anchored_prefix_delimited_line_at[
                nodes, node_index, 1
            ]() else -1
        return -1


def _is_anchored_prefix_delimited_line[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `^ prefix* open dot* close $` for grep line scans."""
    return _anchored_prefix_delimited_line_offset[nodes, node_index]() >= 0


def _is_adjacent_dot_stars_around_literal[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `.*.*literal.*` for linear line-oriented execution."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 4:
            comptime literal = nodes[sequence.items[2]]
            return (
                _is_zero_or_more_dot[nodes, sequence.items[0]]()
                and _is_zero_or_more_dot[nodes, sequence.items[1]]()
                and literal.isa[LiteralNode]()
                and literal[LiteralNode].value.byte_length() > 0
                and _is_zero_or_more_dot[nodes, sequence.items[3]]()
            )
    return False


def _is_greedy_dot_complement_alternation[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize greedy `.*[^class]|[class]` byte alternations."""
    comptime node = nodes[node_index]
    comptime if node.isa[OrNode]():
        comptime alternation = node[OrNode]
        comptime if alternation.count == 2:
            comptime first_node = nodes[alternation.options[0]]
            comptime fallback_node = nodes[alternation.options[1]]
            comptime if (
                first_node.isa[SequenceNode]()
                and fallback_node.isa[BracketClassNode]()
            ):
                comptime first = first_node[SequenceNode]
                comptime fallback = fallback_node[BracketClassNode]
                comptime if first.count == 2:
                    comptime repeat_node = nodes[first.items[0]]
                    comptime terminal_node = nodes[first.items[1]]
                    comptime if (
                        repeat_node.isa[RepeatNode]()
                        and terminal_node.isa[BracketClassNode]()
                    ):
                        comptime repeat = repeat_node[RepeatNode]
                        comptime terminal = terminal_node[BracketClassNode]
                        return Bool(
                            _is_zero_or_more_dot[nodes, first.items[0]]()
                            and repeat.greedy
                            and terminal.negated
                            and not fallback.negated
                            and _same_bracket_ranges[terminal, fallback]()
                            and _bracket_accepts[terminal](ord("\n"))
                        )
    return False


def _prefixed_nested_dot_literal_index[
    nodes: List[RegexNode], node_index: Int
]() -> Int:
    """Return `L` for `required nullable nullable (nullable .* (.*L.*))`."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime root = node[SequenceNode]
        comptime if root.count == 4:
            comptime prefix_node = nodes[root.items[0]]
            comptime nullable_one_node = nodes[root.items[1]]
            comptime nullable_two_node = nodes[root.items[2]]
            comptime tail_node = nodes[root.items[3]]
            comptime if (
                prefix_node.isa[RepeatNode]()
                and nullable_one_node.isa[RepeatNode]()
                and nullable_two_node.isa[RepeatNode]()
                and tail_node.isa[SequenceNode]()
            ):
                comptime prefix = prefix_node[RepeatNode]
                comptime nullable_one = nullable_one_node[RepeatNode]
                comptime nullable_two = nullable_two_node[RepeatNode]
                comptime tail = tail_node[SequenceNode]
                comptime if (
                    prefix.minimum > 0
                    and nullable_one.minimum == 0
                    and nullable_two.minimum == 0
                    and tail.count == 3
                ):
                    comptime decoration_node = nodes[tail.items[0]]
                    comptime core_node = nodes[tail.items[2]]
                    comptime if (
                        decoration_node.isa[RepeatNode]()
                        and core_node.isa[SequenceNode]()
                    ):
                        comptime decoration = decoration_node[RepeatNode]
                        comptime core = core_node[SequenceNode]
                        comptime if decoration.minimum == 0 and core.count == 3:
                            comptime literal_node = nodes[core.items[1]]
                            comptime if literal_node.isa[LiteralNode]():
                                comptime literal = literal_node[LiteralNode]
                                comptime if (
                                    _is_zero_or_more_dot[nodes, tail.items[1]]()
                                    and _is_zero_or_more_dot[
                                        nodes, core.items[0]
                                    ]()
                                    and _is_zero_or_more_dot[
                                        nodes, core.items[2]
                                    ]()
                                    and literal.value.byte_length() > 0
                                ):
                                    return core.items[1]
    return -1


def _is_repeated_lazy_dot_delimiter_suffix[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `(.*?D){n}S` with one-byte literal `D` and `S`."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime root = node[SequenceNode]
        comptime if root.count == 2:
            comptime repeated_node = nodes[root.items[0]]
            comptime suffix_node = nodes[root.items[1]]
            comptime if (
                repeated_node.isa[RepeatNode]()
                and suffix_node.isa[LiteralNode]()
            ):
                comptime repeated = repeated_node[RepeatNode]
                comptime child_node = nodes[repeated.child]
                comptime suffix = suffix_node[LiteralNode]
                comptime if (
                    repeated.minimum > 0
                    and repeated.minimum == repeated.maximum
                    and child_node.isa[SequenceNode]()
                    and suffix.value.byte_length() == 1
                ):
                    comptime child = child_node[SequenceNode]
                    comptime if child.count == 2:
                        comptime dot_node = nodes[child.items[0]]
                        comptime delimiter_node = nodes[child.items[1]]
                        comptime if (
                            dot_node.isa[RepeatNode]()
                            and delimiter_node.isa[LiteralNode]()
                        ):
                            comptime dot = dot_node[RepeatNode]
                            comptime delimiter = delimiter_node[LiteralNode]
                            comptime dot_child = nodes[dot.child]
                            comptime if not dot_child.isa[CharClassNode]():
                                return False
                            return Bool(
                                dot.minimum == 0
                                and dot.maximum == -1
                                and not dot.greedy
                                and dot_child[CharClassNode].kind
                                == CHAR_BYTE_DOT
                                and delimiter.value.byte_length() == 1
                            )
    return False


@fieldwise_init
struct _TwoDelimiterBracketRunsPlan(Copyable):
    var first_delimiter_index: Int
    var left_child: Int
    var middle_child: Int
    var left_minimum: Int
    var middle_minimum: Int
    var second_byte: Int


def _two_delimiter_bracket_runs_plan[
    nodes: List[RegexNode], node_index: Int
]() -> Optional[_TwoDelimiterBracketRunsPlan]:
    """Extract the pieces of `A+D B+D+` when all runs are byte brackets."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 5:
            comptime left_node = nodes[sequence.items[0]]
            comptime first_delimiter_node = nodes[sequence.items[1]]
            comptime middle_node = nodes[sequence.items[2]]
            comptime second_delimiter_node = nodes[sequence.items[3]]
            comptime right_node = nodes[sequence.items[4]]
            comptime if (
                left_node.isa[RepeatNode]()
                and first_delimiter_node.isa[LiteralNode]()
                and middle_node.isa[RepeatNode]()
                and second_delimiter_node.isa[LiteralNode]()
                and right_node.isa[RepeatNode]()
            ):
                comptime left = left_node[RepeatNode]
                comptime middle = middle_node[RepeatNode]
                comptime right = right_node[RepeatNode]
                comptime first_delimiter = first_delimiter_node[LiteralNode]
                comptime second_delimiter = second_delimiter_node[LiteralNode]
                comptime left_child = nodes[left.child]
                comptime middle_child = nodes[middle.child]
                comptime right_child = nodes[right.child]
                comptime if (
                    left_child.isa[BracketClassNode]()
                    and middle_child.isa[BracketClassNode]()
                    and right_child.isa[BracketClassNode]()
                ):
                    comptime middle_bracket = middle_child[BracketClassNode]
                    comptime right_bracket = right_child[BracketClassNode]
                    comptime if (
                        left.minimum == 1
                        and left.maximum == -1
                        and left.greedy
                        and middle.minimum == 1
                        and middle.maximum == -1
                        and middle.greedy
                        and right.minimum == 1
                        and right.maximum == -1
                        and right.greedy
                        and first_delimiter.value.byte_length() == 1
                        and second_delimiter.value.byte_length() == 1
                        and middle_bracket.negated == right_bracket.negated
                        and _same_bracket_ranges[
                            middle_bracket, right_bracket
                        ]()
                    ):
                        return _TwoDelimiterBracketRunsPlan(
                            first_delimiter_index=sequence.items[1],
                            left_child=left.child,
                            middle_child=middle.child,
                            left_minimum=left.minimum,
                            middle_minimum=middle.minimum,
                            second_byte=Int(
                                second_delimiter.value.as_bytes()[0]
                            ),
                        )
    return None


def _is_leading_class_literal_search[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    """Recognize `class* literal ($|.*)` for reverse-prefix matching."""
    comptime node = nodes[node_index]
    comptime if node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime if sequence.count == 3:
            comptime prefix = nodes[sequence.items[0]]
            comptime middle = nodes[sequence.items[1]]
            comptime if prefix.isa[RepeatNode]() and middle.isa[LiteralNode]():
                comptime repeat = prefix[RepeatNode]
                comptime if middle[LiteralNode].value.byte_length() > 0:
                    return (
                        repeat.maximum == -1
                        and _is_one_byte_class_node[nodes, repeat.child]()
                    ) and (
                        _is_end_assertion_node[nodes, sequence.items[2]]()
                        or _is_zero_or_more_dot[nodes, sequence.items[2]]()
                    )
    return False


@always_inline
def _one_byte_atom_accepts[
    nodes: List[RegexNode], node_index: Int
](value: Int) -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return value == Int(node[LiteralNode].value.as_bytes()[0])
    elif node.isa[CharClassNode]():
        return _accepts_class[node[CharClassNode].kind](value)
    else:
        return _bracket_accepts[node[BracketClassNode]](value)


@always_inline
def _bounded_repeat_byte_accepts[
    nodes: List[RegexNode], node_index: Int
](value: Int) -> Bool:
    """Use a single folded range test for the common `[A-Za-z]` class."""
    comptime node = nodes[node_index]
    comptime if node.isa[BracketClassNode]():
        comptime if _is_ascii_letters[node[BracketClassNode]]():
            var folded = value | 0x20
            return ord("a") <= folded <= ord("z")
    return _one_byte_atom_accepts[nodes, node_index](value)


@always_inline
def _fixed_repeat_mask[
    nodes: List[RegexNode],
    repeat: RepeatNode,
    width: Int,
    repetition: Int,
    pattern_offset: Int,
](text: ImmStringSpan, block_start: Int) -> SIMD[.bool, width]:
    comptime if repetition == repeat.minimum:
        return SIMD[.bool, width](fill=True)
    else:
        comptime child_width = _fixed_node_width[nodes, repeat.child]()
        return _fixed_node_mask[
            nodes,
            repeat.child,
            width,
            pattern_offset + repetition * child_width,
        ](text, block_start) & _fixed_repeat_mask[
            nodes,
            repeat,
            width,
            repetition + 1,
            pattern_offset,
        ](
            text, block_start
        )


@always_inline
def _fixed_sequence_mask[
    nodes: List[RegexNode],
    sequence: SequenceNode,
    width: Int,
    item: Int,
    pattern_offset: Int,
](text: ImmStringSpan, block_start: Int) -> SIMD[.bool, width]:
    comptime if item == sequence.count:
        return SIMD[.bool, width](fill=True)
    else:
        comptime child = sequence.items[item]
        comptime child_width = _fixed_node_width[nodes, child]()
        return _fixed_node_mask[nodes, child, width, pattern_offset](
            text, block_start
        ) & _fixed_sequence_mask[
            nodes,
            sequence,
            width,
            item + 1,
            pattern_offset + child_width,
        ](
            text, block_start
        )


@always_inline
def _fixed_node_mask[
    nodes: List[RegexNode], node_index: Int, width: Int, pattern_offset: Int
](text: ImmStringSpan, block_start: Int) -> SIMD[.bool, width]:
    """Evaluate `width` fixed-width match starts in parallel."""
    comptime node = nodes[node_index]
    comptime if node.isa[EmptyNode]():
        return SIMD[.bool, width](fill=True)
    elif node.isa[LiteralNode]():
        comptime literal = node[LiteralNode]
        var matched = SIMD[.bool, width](fill=True)
        comptime for i in range(literal.value.byte_length()):
            var values = text.unsafe_ptr().unsafe_load[
                width=width, alignment=1
            ](block_start + pattern_offset + i)
            comptime expected = literal.value.as_bytes()[i]
            matched &= values.eq(SIMD[.uint8, width](expected))
        return matched
    elif node.isa[CharClassNode]():
        comptime char_class = node[CharClassNode]
        var values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
            block_start + pattern_offset
        )
        return _class_mask[char_class.kind, width](values)
    elif node.isa[BracketClassNode]():
        comptime bracket = node[BracketClassNode]
        var values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
            block_start + pattern_offset
        )
        return _bracket_mask[bracket, width](values)
    elif node.isa[RepeatNode]():
        return _fixed_repeat_mask[
            nodes, node[RepeatNode], width, 0, pattern_offset
        ](text, block_start)
    elif node.isa[SequenceNode]():
        return _fixed_sequence_mask[
            nodes, node[SequenceNode], width, 0, pattern_offset
        ](text, block_start)
    elif node.isa[OrNode]():
        var matched = SIMD[.bool, width](fill=False)
        comptime alternation = node[OrNode]
        comptime for i in range(alternation.count):
            matched |= _fixed_node_mask[
                nodes, alternation.options[i], width, pattern_offset
            ](text, block_start)
        return matched
    return SIMD[.bool, width](fill=False)


@always_inline
def _fixed_sequence_offset_mask[
    nodes: List[RegexNode],
    sequence: SequenceNode,
    width: Int,
    item: Int,
    target: Int,
](text: ImmStringSpan, block_start: Int) -> SIMD[.bool, width]:
    comptime child = sequence.items[item]
    comptime child_width = _fixed_node_width[nodes, child]()
    comptime if target < child_width:
        return _fixed_offset_mask[nodes, child, width, target](
            text, block_start
        )
    return _fixed_sequence_offset_mask[
        nodes, sequence, width, item + 1, target - child_width
    ](text, block_start + child_width)


@always_inline
def _fixed_offset_mask[
    nodes: List[RegexNode], node_index: Int, width: Int, target: Int
](text: ImmStringSpan, block_start: Int) -> SIMD[.bool, width]:
    """Evaluate one byte predicate at a fixed offset for many starts."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        var values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
            block_start + target
        )
        return values.eq(
            SIMD[.uint8, width](node[LiteralNode].value.as_bytes()[target])
        )
    elif node.isa[CharClassNode]():
        var values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
            block_start
        )
        return _class_mask[node[CharClassNode].kind, width](values)
    elif node.isa[BracketClassNode]():
        var values = text.unsafe_ptr().unsafe_load[width=width, alignment=1](
            block_start
        )
        return _bracket_mask[node[BracketClassNode], width](values)
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime child_width = _fixed_node_width[nodes, repeat.child]()
        return _fixed_offset_mask[
            nodes, repeat.child, width, target % child_width
        ](text, block_start + target - target % child_width)
    elif node.isa[OrNode]():
        var accepted = SIMD[.bool, width](fill=False)
        comptime alternation = node[OrNode]
        comptime for i in range(alternation.count):
            accepted |= _fixed_offset_mask[
                nodes, alternation.options[i], width, target
            ](text, block_start)
        return accepted
    else:
        return _fixed_sequence_offset_mask[
            nodes, node[SequenceNode], width, 0, target
        ](text, block_start)


def _fixed_sequence_offset_coverage[
    nodes: List[RegexNode],
    sequence: SequenceNode,
    item: Int,
    target: Int,
]() -> Int:
    comptime child = sequence.items[item]
    comptime child_width = _fixed_node_width[nodes, child]()
    comptime if target < child_width:
        return _fixed_offset_coverage[nodes, child, target]()
    return _fixed_sequence_offset_coverage[
        nodes, sequence, item + 1, target - child_width
    ]()


def _fixed_offset_coverage[
    nodes: List[RegexNode], node_index: Int, target: Int
]() -> Int:
    """Return the accepted-byte count for one fixed expression offset."""
    comptime node = nodes[node_index]
    comptime if node.isa[LiteralNode]():
        return 1
    elif node.isa[CharClassNode]() or node.isa[BracketClassNode]():
        return _one_byte_node_coverage[nodes, node_index]()
    elif node.isa[RepeatNode]():
        comptime repeat = node[RepeatNode]
        comptime child_width = _fixed_node_width[nodes, repeat.child]()
        return _fixed_offset_coverage[
            nodes, repeat.child, target % child_width
        ]()
    elif node.isa[OrNode]():
        comptime alternation = node[OrNode]
        var coverage = 257
        comptime for i in range(alternation.count):
            coverage = min(
                coverage,
                _fixed_offset_coverage[nodes, alternation.options[i], target](),
            )
        return coverage
    else:
        return _fixed_sequence_offset_coverage[
            nodes, node[SequenceNode], 0, target
        ]()


@fieldwise_init
struct _FixedPrefilterPlan(Copyable):
    var first: Int
    var second: Int
    var third: Int
    var fourth: Int
    var fifth: Int


def _fixed_node_contains_alternation[
    nodes: List[RegexNode], node_index: Int
]() -> Bool:
    comptime node = nodes[node_index]
    comptime if node.isa[OrNode]():
        return True
    elif node.isa[RepeatNode]():
        return _fixed_node_contains_alternation[nodes, node[RepeatNode].child]()
    elif node.isa[SequenceNode]():
        comptime sequence = node[SequenceNode]
        comptime for i in range(sequence.count):
            comptime if _fixed_node_contains_alternation[
                nodes, sequence.items[i]
            ]():
                return True
    return False


def _fixed_prefilter_plan[
    nodes: List[RegexNode], node_index: Int, match_width: Int
]() -> _FixedPrefilterPlan:
    """Choose the five narrowest byte predicates in a fixed expression."""
    var first = 0
    var second = -1
    var third = -1
    var fourth = -1
    var fifth = -1
    var first_coverage = 257
    var second_coverage = 257
    var third_coverage = 257
    var fourth_coverage = 257
    var fifth_coverage = 257
    comptime for offset in range(match_width):
        comptime coverage = _fixed_offset_coverage[nodes, node_index, offset]()
        if coverage < first_coverage:
            fifth = fourth
            fifth_coverage = fourth_coverage
            fourth = third
            fourth_coverage = third_coverage
            third = second
            third_coverage = second_coverage
            second = first
            second_coverage = first_coverage
            first = offset
            first_coverage = coverage
        elif coverage < second_coverage:
            fifth = fourth
            fifth_coverage = fourth_coverage
            fourth = third
            fourth_coverage = third_coverage
            third = second
            third_coverage = second_coverage
            second = offset
            second_coverage = coverage
        elif coverage < third_coverage:
            fifth = fourth
            fifth_coverage = fourth_coverage
            fourth = third
            fourth_coverage = third_coverage
            third = offset
            third_coverage = coverage
        elif coverage < fourth_coverage:
            fifth = fourth
            fifth_coverage = fourth_coverage
            fourth = offset
            fourth_coverage = coverage
        elif coverage < fifth_coverage:
            fifth = offset
            fifth_coverage = coverage
    return _FixedPrefilterPlan(first, second, third, fourth, fifth)
