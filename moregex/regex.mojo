"""Public compile-time-specialized regex API."""

from ._ast import (
    CHAR_UNICODE_DOT,
    BracketClassNode,
    CharClassNode,
    LiteralNode,
    OrNode,
    RepeatNode,
    SequenceNode,
)
from ._syntax import Regex

from ._regex_common import (
    CLASS_TAIL_SIMD_WIDTH,
    _match_checksum,
    _static_source_is_root_literal,
)

from ._regex_analysis import (
    _anchored_lazy_literal_plan,
    _all_captures_mandatory,
    _constant_capture_count,
    _all_casefold_prefixed_sequence_options,
    _all_literal_options,
    _all_prefixed_sequence_options,
    _count_unicode_dot,
    _fixed_node_width,
    _is_adjacent_dot_stars_around_literal,
    _is_anchored_prefix_delimited_line,
    _is_bounded_capitalized_word_sequence,
    _is_bounded_prefix_literal_alternation,
    _is_class_literal_alternation_with_suffix,
    _is_greedy_dot_complement_alternation,
    _is_leading_class_literal_search,
    _is_multiline_literal_edge_alternation,
    _is_multiline_whole_line,
    _is_nested_run_then_disjoint_class,
    _is_one_byte_class_node,
    _is_repeated_lazy_dot_delimiter_suffix,
    _is_reverse_suffix_class_sequence,
    _is_start_anchored,
    _is_symmetric_bounded_delimited_sequence,
    _is_unicode_dotall_plus,
    _is_whole_input_dotall_star,
    _leading_repeat_literal_item,
    _line_prefix_run_literal_plan,
    _literal_bytes_all_accepted_by_node,
    _prefixed_nested_dot_literal_index,
    _two_delimiter_bracket_runs_plan,
    _unicode_dot_kind,
)
from ._regex_find import (
    _has_leading_literal_prefilter,
    _is_anchored_lazy_capture_record,
    _is_delimited_capture_record,
    _is_delimited_capture_record_with_optional_tail,
    _is_fixed_capture_sequence,
    _matches_anchored_lazy_capture_record,
    _prefilter_start,
    find_span,
)

from ._regex_matcher import (
    _match_node,
    matches,
    matches_span,
)
from ._regex_nfa import (
    _nfa_find_capture_participation,
    _nfa_find_from,
    _nfa_match_at,
    _nfa_search_from,
)
from ._regex_count import (
    _count_anchored_lazy_literal_lines,
    _count_adjacent_dot_stars_around_literal,
    _count_anchored_prefix_delimited_lines,
    _count_bounded_capitalized_word_sequence,
    _count_bounded_prefix_literal_alternation,
    _count_bracket_prefixed_sequence,
    _count_class_literal_alternation_with_suffix,
    _count_end_anchored_fixed,
    _count_fixed_width_prefiltered,
    _count_greedy_dot_complement_alternation,
    _count_greedy_run_literal_suffix,
    _count_leading_class_literal,
    _count_line_prefix_run_literal,
    _count_multiline_literal_edge_alternation,
    _count_nested_run_then_disjoint_class,
    _count_one_byte_atom,
    _count_one_byte_class_repeat,
    _count_prefixed_alternation,
    _count_prefixed_alternation_simd,
    _count_prefixed_nested_dot_literal,
    _count_repeated_lazy_dot_delimiter_suffix,
    _count_reverse_suffix_class,
    _count_simple_class_anchor,
    _count_simple_infix,
    _count_two_delimiter_bracket_runs,
    _search_one_byte_class_repeat,
    _search_fixed_width_prefiltered,
    _search_simple_infix,
    _search_simple_class_anchor,
)
from ._regex_count_casefold import _count_casefold_prefixed_alternation
from ._regex_count_literal import (
    _count_edge_prefiltered_literal,
    _count_reverse_unbordered_literal,
    _count_short_literal_simd_candidates,
    _count_static_literal,
    _count_unique_anchor_literal,
    _literal_has_unique_first_byte,
    _literal_unique_high_byte_offset,
    _search_static_literal,
)
from ._regex_scan import _scan_generic
from ._regex_search import (
    _all_infix_options,
    _count_long_word,
    _count_word_boundary_wrapped,
    _count_word_run_literal_suffix,
    _is_bracket_infix_search,
    _is_long_word_search,
    _is_literal_dot_infix,
    _is_numeric_date_search,
    _is_prefixed_infix_search,
    _is_word_boundary_wrapped,
    _is_word_run_literal_suffix,
    _grep_prefixed_infix,
    _search_bracket_infix,
    _search_infix_alternation,
    _search_literal_dot_infix,
    _search_long_word,
    _search_numeric_date,
    _search_prefixed_infix,
    _search_word_boundary_wrapped,
    _word_boundary_inner_index,
)
from ._regex_literals import (
    _count_literal_alternation,
    _search_literal_alternation,
)
from ._regex_plan import _execution_plan
from ._regex_tuning import (
    DELIMITED_REPEAT_PLAN_MINIMUM,
    GREEDY_RUN_SUFFIX_HAYSTACK_BYTES,
    LARGE_LITERAL_HAYSTACK_BYTES,
    REVERSE_LITERAL_MIN_BYTES,
    SHORT_LITERAL_MAX_BYTES,
    SHORT_LITERAL_MIN_BYTES,
)
from ._regex_utf8_runs import (
    _count_exact_utf8_class_sequence,
    _count_utf8_byte_class_repeat,
    _count_utf8_class_literal_infix_alternation,
    _count_utf8_class_separated_literal_infix,
    _is_exact_utf8_class_sequence,
    _is_utf8_byte_class_repeat,
    _is_utf8_class_literal_infix_alternation,
    _is_utf8_class_separated_literal_infix,
)


@always_inline
def _search_planned[regex: Regex](text: ImmStringSpan) -> Bool:
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        comptime if _static_source_is_root_literal[regex]():
            return _search_static_literal[regex.source](text)
        return text.find(root[LiteralNode].value) >= 0
    comptime plan = _execution_plan[regex]()
    if plan.rejects_length(text.byte_length()):
        return False
    comptime if _is_exact_utf8_class_sequence[regex.nodes, regex.root]():
        return (
            _count_exact_utf8_class_sequence[regex, False](text.as_bytes()) > 0
        )
    comptime if _is_literal_dot_infix[regex.nodes, root]():
        return _search_literal_dot_infix[regex.nodes, root](text)
    comptime if plan.requires_ordered_nfa:
        # An exact leading literal identifies complete match starts. Avoid
        # keeping an unanchored NFA active at every byte when those starts are
        # sparse; run the ordered automaton only at literal candidates.
        comptime if (
            not plan.start_anchored and _has_leading_literal_prefilter[regex]()
        ):
            var candidate = _prefilter_start[regex](text, 0)
            if candidate < 0:
                return False
            if _nfa_match_at[regex](text, candidate):
                return True
            # Repeated anchored attempts can become quadratic when the prefix
            # is dense. The first candidate is now disproven, so resume the
            # linear unanchored executor immediately after it.
            return _nfa_search_from[regex](text, candidate + 1)
        return _nfa_search_from[regex](text, 0)
    comptime if plan.start_anchored:
        return Bool(_match_node[regex.nodes, regex.root](text, 0))
    comptime if _is_multiline_whole_line[regex.nodes, regex.root]():
        return True
    comptime if root.isa[RepeatNode]():
        comptime repeat = root[RepeatNode]
        comptime if repeat.minimum > 0 and _is_one_byte_class_node[
            regex.nodes, repeat.child
        ]():
            return _search_one_byte_class_repeat[regex](text)
    # Boundary assertions around a required word run do not change Boolean
    # existence: every maximal ASCII-word run supplies both boundaries.
    comptime if _is_long_word_search[regex.nodes, root]():
        return _search_long_word[regex.nodes, root](text)
    comptime if root.isa[OrNode]():
        comptime alternation = root[OrNode]
        comptime if _is_utf8_class_literal_infix_alternation[
            regex.nodes, regex.root
        ]():
            return (
                _count_utf8_class_literal_infix_alternation[regex, False](text)
                > 0
            )
        comptime if _is_greedy_dot_complement_alternation[
            regex.nodes, regex.root
        ]():
            return (
                _count_greedy_dot_complement_alternation[regex, False](text) > 0
            )
        comptime if _is_multiline_literal_edge_alternation[
            regex.nodes, regex.root
        ]():
            return (
                _count_multiline_literal_edge_alternation[regex, False](text)
                > 0
            )
        comptime if _all_literal_options[regex.nodes, alternation]():
            return _search_literal_alternation[regex.nodes, alternation](text)
        comptime if _all_infix_options[regex.nodes, alternation]():
            return _search_infix_alternation[regex.nodes, alternation](text)
        comptime if _all_casefold_prefixed_sequence_options[
            regex.nodes, alternation
        ]():
            return (
                _count_casefold_prefixed_alternation[regex, alternation, False](
                    text
                )
                > 0
            )
        comptime if _all_prefixed_sequence_options[regex.nodes, alternation]():
            return (
                _count_prefixed_alternation[regex, alternation, False](text) > 0
            )
    comptime if _is_numeric_date_search[regex.nodes, root]():
        return _search_numeric_date[regex.nodes, root](text)
    comptime if _is_bracket_infix_search[regex.nodes, root]():
        return _search_bracket_infix[regex.nodes, root](text)
    comptime if plan.required_literal_index < 0 and _is_word_boundary_wrapped[
        regex.nodes, root
    ]():
        return _search_word_boundary_wrapped[regex](text)
    comptime if plan.fixed_width > 0:
        return _search_fixed_width_prefiltered[regex, plan.fixed_width](text)
    comptime if plan.simple_infix_item >= 0:
        return _search_simple_infix[regex, plan.simple_infix_item](text)
    comptime if plan.simple_class_item >= 0:
        return _search_simple_class_anchor[regex, plan.simple_class_item](text)
    return _scan_generic[regex, False, True](text) > 0


@always_inline
def _search_span_impl[regex: Regex](text: ImmStringSpan) -> Bool:
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        comptime literal = root[LiteralNode]
        comptime if _static_source_is_root_literal[regex]():
            return _search_static_literal[regex.source](text)
        return text.find(literal.value) >= 0
    comptime if _is_prefixed_infix_search[regex.nodes, root]():
        return _search_prefixed_infix[regex.nodes, root](text)
    return _search_planned[regex](text)


@always_inline
def search[regex: Regex](text: String) -> Bool:
    """Return whether compile-time `regex` matches anywhere in `text`."""
    return _search_span_impl[regex](text[byte = 0 : text.byte_length()])


@always_inline
def search_span[regex: Regex](text: ImmStringSpan) -> Bool:
    """Search a borrowed string span without allocation."""
    return _search_span_impl[regex](text)


@always_inline
def _count_nfa[regex: Regex, sum_spans: Bool](text: ImmStringSpan) -> Int:
    """Count ordered leftmost, non-overlapping Thompson-NFA matches."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[OrNode]():
        comptime alternation = root[OrNode]
        comptime if _all_prefixed_sequence_options[
            regex.nodes, alternation, 3
        ]():
            return _count_prefixed_alternation_simd[
                regex, alternation, sum_spans, True
            ](text)
    var total = 0
    var search_start = 0
    while search_start <= text.byte_length():
        var result = _nfa_find_from[regex](text, search_start)
        if not result:
            break
        var found = result.unsafe_value()
        total += _match_checksum[sum_spans](found.consumed())
        search_start = found.start + max(1, found.consumed())
    return total


@always_inline
def _count_planned[regex: Regex, sum_spans: Bool](text: ImmStringSpan) -> Int:
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        return _count_literal_root[regex, sum_spans](text)
    comptime if root.isa[OrNode]():
        comptime alternation = root[OrNode]
        comptime if _is_utf8_class_literal_infix_alternation[
            regex.nodes, regex.root
        ]():
            return _count_utf8_class_literal_infix_alternation[
                regex, sum_spans
            ](text)
        comptime if _is_greedy_dot_complement_alternation[
            regex.nodes, regex.root
        ]():
            return _count_greedy_dot_complement_alternation[regex, sum_spans](
                text
            )
        comptime if _is_multiline_literal_edge_alternation[
            regex.nodes, regex.root
        ]():
            return _count_multiline_literal_edge_alternation[regex, sum_spans](
                text
            )
        comptime if _all_literal_options[regex.nodes, alternation]():
            return _count_literal_alternation[
                regex.nodes, alternation, sum_spans
            ](text)
        comptime if _all_casefold_prefixed_sequence_options[
            regex.nodes, alternation
        ]():
            return _count_casefold_prefixed_alternation[
                regex, alternation, sum_spans
            ](text)
        comptime alternation_width = _fixed_node_width[
            regex.nodes, regex.root
        ]()
        comptime if alternation_width > 0:
            return _count_fixed_width_prefiltered[
                regex, alternation_width, sum_spans
            ](text)
        comptime if _all_prefixed_sequence_options[regex.nodes, alternation]():
            return _count_prefixed_alternation[regex, alternation, sum_spans](
                text
            )
    # Keep direct planner callers on the same constant-time/SIMD primitives
    # as public dispatch for fundamental Unicode-dot shapes.  These are
    # execution properties, not workload-specific pattern kernels.
    comptime unicode_dot_kind = _unicode_dot_kind[regex.nodes, regex.root]()
    comptime if unicode_dot_kind >= 0:
        return _count_unicode_dot[
            unicode_dot_kind == CHAR_UNICODE_DOT, sum_spans
        ](text)
    comptime if _is_unicode_dotall_plus[regex.nodes, regex.root]():
        if text.byte_length() == 0:
            return 0
        comptime if sum_spans:
            return text.byte_length()
        return 1
    comptime if _is_whole_input_dotall_star[regex.nodes, regex.root]():
        comptime if sum_spans:
            return text.byte_length()
        return 1 if text.byte_length() == 0 else 2
    comptime nested_dot_literal = _prefixed_nested_dot_literal_index[
        regex.nodes, regex.root
    ]()
    comptime if nested_dot_literal >= 0:
        return _count_prefixed_nested_dot_literal[
            regex, nested_dot_literal, sum_spans
        ](text)
    # A root repeat over a byte predicate is a generic run-counting problem.
    # Consume maximal runs once instead of invoking the matcher at every byte.
    comptime if root.isa[RepeatNode]():
        comptime repeat = root[RepeatNode]
        comptime if repeat.minimum > 0 and _is_one_byte_class_node[
            regex.nodes, repeat.child
        ]():
            return _count_one_byte_class_repeat[regex, sum_spans](text)
        comptime if _is_utf8_byte_class_repeat[regex.nodes, regex.root]():
            return _count_utf8_byte_class_repeat[regex, sum_spans](
                text.as_bytes()
            )
    comptime if _is_exact_utf8_class_sequence[regex.nodes, regex.root]():
        return _count_exact_utf8_class_sequence[regex, sum_spans](
            text.as_bytes()
        )
    comptime if _is_utf8_class_separated_literal_infix[
        regex.nodes, regex.root
    ]():
        return _count_utf8_class_separated_literal_infix[regex, sum_spans](text)
    comptime if _is_nested_run_then_disjoint_class[regex.nodes, regex.root]():
        return _count_nested_run_then_disjoint_class[regex, sum_spans](text)
    comptime if _is_bounded_capitalized_word_sequence[
        regex.nodes, regex.root
    ]():
        return _count_bounded_capitalized_word_sequence[regex, sum_spans](text)
    comptime if _is_long_word_search[regex.nodes, root]():
        return _count_long_word[regex, sum_spans](text)
    comptime if _is_word_run_literal_suffix[regex.nodes, root]():
        return _count_word_run_literal_suffix[regex, sum_spans](text)
    comptime if _is_word_boundary_wrapped[regex.nodes, root]():
        comptime boundary_inner = _word_boundary_inner_index[
            regex.nodes, root
        ]()
        comptime boundary_child = regex.nodes[boundary_inner]
        comptime if boundary_child.isa[OrNode]():
            comptime boundary_alternation = boundary_child[OrNode]
            comptime if _all_casefold_prefixed_sequence_options[
                regex.nodes, boundary_alternation
            ]():
                return _count_casefold_prefixed_alternation[
                    regex, boundary_alternation, sum_spans, True
                ](text)
    # Treat word boundaries as a generic candidate source for any wrapped
    # expression; test only actual boundary positions instead of every byte.
    comptime if _is_word_boundary_wrapped[regex.nodes, root]():
        return _count_word_boundary_wrapped[regex, sum_spans](text)
    comptime if _is_adjacent_dot_stars_around_literal[
        regex.nodes, regex.root
    ]():
        return _count_adjacent_dot_stars_around_literal[regex, sum_spans](text)
    # Drive class-star/literal searches from the required literal instead of
    # retrying the variable-width prefix at every byte.  This is the generic
    # candidate plan for `[class]* literal ($|.*)` sequences.
    comptime if _is_leading_class_literal_search[regex.nodes, regex.root]():
        return _count_leading_class_literal[regex, sum_spans](text)
    comptime if _is_bounded_prefix_literal_alternation[
        regex.nodes, regex.root
    ]():
        return _count_bounded_prefix_literal_alternation[regex, sum_spans](text)
    comptime if _is_class_literal_alternation_with_suffix[
        regex.nodes, regex.root
    ]():
        return _count_class_literal_alternation_with_suffix[regex, sum_spans](
            text
        )
    comptime if _is_symmetric_bounded_delimited_sequence[
        regex.nodes, regex.root
    ]():
        comptime delimited_sequence = root[SequenceNode]
        comptime delimited_repeat = regex.nodes[delimited_sequence.items[1]][
            RepeatNode
        ]
        comptime if delimited_repeat.maximum >= DELIMITED_REPEAT_PLAN_MINIMUM:
            return _count_bracket_prefixed_sequence[regex, sum_spans](text)
    comptime if _is_repeated_lazy_dot_delimiter_suffix[
        regex.nodes, regex.root
    ]():
        return _count_repeated_lazy_dot_delimiter_suffix[regex, sum_spans](text)
    comptime delimiter_runs = _two_delimiter_bracket_runs_plan[
        regex.nodes, regex.root
    ]()
    comptime if delimiter_runs:
        return _count_two_delimiter_bracket_runs[
            regex, delimiter_runs.unsafe_value(), sum_spans
        ](text)
    comptime run_suffix = _leading_repeat_literal_item[
        regex.nodes, regex.root, False
    ]()
    comptime if run_suffix >= 0:
        comptime sequence = root[SequenceNode]
        comptime repeat = regex.nodes[sequence.items[0]][RepeatNode]
        comptime literal = regex.nodes[sequence.items[run_suffix]][LiteralNode]
        comptime if (
            sequence.count == 2
            and repeat.maximum == -1
            and repeat.greedy
            and _literal_bytes_all_accepted_by_node[
                regex.nodes, repeat.child, literal.value, 0
            ]()
        ):
            if text.byte_length() >= GREEDY_RUN_SUFFIX_HAYSTACK_BYTES:
                return _count_greedy_run_literal_suffix[regex, sum_spans](text)
    comptime leading_literal = _leading_repeat_literal_item[
        regex.nodes, regex.root
    ]()
    comptime if leading_literal >= 0:
        return _count_simple_infix[regex, leading_literal, sum_spans](text)
    # A long literal between a leading byte predicate and a variable byte run
    # is selective enough to justify driving the match from its terminal
    # predicate. Short literals stay on the ordinary literal-anchor planner.
    comptime if _is_reverse_suffix_class_sequence[regex.nodes, regex.root]():
        comptime reverse_sequence = root[SequenceNode]
        comptime reverse_literal = regex.nodes[reverse_sequence.items[1]][
            LiteralNode
        ]
        comptime if reverse_literal.value.byte_length() >= REVERSE_LITERAL_MIN_BYTES:
            return _count_reverse_suffix_class[regex, sum_spans](text)
    comptime plan = _execution_plan[regex]()
    if plan.rejects_length(text.byte_length()):
        return 0
    comptime if plan.requires_ordered_nfa:
        return _count_nfa[regex, sum_spans](text)
    comptime if plan.start_anchored:
        var anchored = _match_node[regex.nodes, regex.root](text, 0)
        if anchored:
            return _match_checksum[sum_spans](
                anchored.unsafe_value().consumed()
            )
        return 0
    comptime if plan.end_anchored_width >= 0:
        return _count_end_anchored_fixed[
            regex, plan.end_anchored_width, sum_spans
        ](text)
    comptime if plan.fixed_width > 0:
        return _count_fixed_width_prefiltered[
            regex, plan.fixed_width, sum_spans
        ](text)
    comptime if plan.simple_infix_item >= 0:
        return _count_simple_infix[regex, plan.simple_infix_item, sum_spans](
            text
        )
    comptime if plan.simple_class_item >= 0:
        return _count_simple_class_anchor[
            regex, plan.simple_class_item, sum_spans
        ](text)
    return _scan_generic[regex, sum_spans, False](text)


@always_inline
def _count_literal_root[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    comptime literal = regex.nodes[regex.root][LiteralNode]
    comptime literal_length = literal.value.byte_length()
    comptime if literal_length == 0:
        comptime if sum_spans:
            return 0
        return text.byte_length() + 1
    comptime if literal_length == 1:
        return _count_one_byte_atom[regex](text)
    comptime unique_first = _literal_has_unique_first_byte[literal.value]()
    comptime if (
        SHORT_LITERAL_MIN_BYTES <= literal_length <= SHORT_LITERAL_MAX_BYTES
        and unique_first
        and _static_source_is_root_literal[regex]()
    ):
        var short_candidate_count = text.byte_length() - literal_length + 1
        if (
            CLASS_TAIL_SIMD_WIDTH
            <= short_candidate_count
            <= 2 * CLASS_TAIL_SIMD_WIDTH
        ):
            return _count_short_literal_simd_candidates[
                regex.source, sum_spans
            ](text)
    comptime high_anchor = _literal_unique_high_byte_offset[literal.value]()
    comptime if high_anchor >= 0:
        if text.byte_length() >= LARGE_LITERAL_HAYSTACK_BYTES:
            return _count_unique_anchor_literal[
                literal.value, high_anchor, sum_spans
            ](text)
    comptime if literal_length >= SHORT_LITERAL_MIN_BYTES and unique_first:
        if text.byte_length() >= LARGE_LITERAL_HAYSTACK_BYTES:
            return _count_reverse_unbordered_literal[literal.value, sum_spans](
                text
            )
    comptime if literal_length >= 2:
        if text.byte_length() >= LARGE_LITERAL_HAYSTACK_BYTES:
            return _count_edge_prefiltered_literal[literal.value, sum_spans](
                text
            )
    comptime if _static_source_is_root_literal[regex]():
        return _count_static_literal[regex.source, sum_spans](text)
    var start = text.find(literal.value)
    if start < 0:
        return 0
    var total = _match_checksum[sum_spans](literal_length)
    while start + 2 * literal_length <= text.byte_length():
        var next_start = start + literal_length
        start = text.find(literal.value, next_start)
        if start < 0:
            break
        total += _match_checksum[sum_spans](literal_length)
    return total


@always_inline
def _count_impl[regex: Regex, sum_spans: Bool](text: ImmStringSpan) -> Int:
    """Compute a match count or matched-byte checksum."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        return _count_literal_root[regex, sum_spans](text)
    comptime unicode_dot_kind = _unicode_dot_kind[regex.nodes, regex.root]()
    comptime if unicode_dot_kind >= 0:
        return _count_planned[regex, sum_spans](text)
    comptime if root.isa[CharClassNode]() or root.isa[BracketClassNode]():
        return _count_one_byte_atom[regex](text)
    comptime if _is_unicode_dotall_plus[regex.nodes, regex.root]():
        if text.byte_length() == 0:
            return 0
        comptime if sum_spans:
            return text.byte_length()
        return 1
    comptime if _is_whole_input_dotall_star[regex.nodes, regex.root]():
        comptime if sum_spans:
            return text.byte_length()
        return 1 if text.byte_length() == 0 else 2
    comptime if root.isa[RepeatNode]():
        comptime repeat = root[RepeatNode]
        comptime if (
            repeat.minimum > 0
            and _is_one_byte_class_node[regex.nodes, repeat.child]()
        ):
            return _count_one_byte_class_repeat[regex, sum_spans](text)
        return _count_planned[regex, sum_spans](text)
    comptime if _is_start_anchored[regex.nodes, regex.root]():
        return _count_planned[regex, sum_spans](text)
    # Keep the direct call here: an extra planner inlining layer measured
    # materially slower for this otherwise shared generic anchor executor.
    comptime if _is_word_run_literal_suffix[regex.nodes, root]():
        return _count_word_run_literal_suffix[regex, sum_spans](text)
    return _count_planned[regex, sum_spans](text)


@always_inline
def count_spans[regex: Regex](text: String) -> Int:
    """Sum byte lengths of leftmost, non-overlapping matches in `text`."""
    return _count_impl[regex, True](text[byte = 0 : text.byte_length()])


@always_inline
def count_spans_span[regex: Regex](text: ImmStringSpan) -> Int:
    """Borrowed-input version of `count_spans`."""
    return _count_impl[regex, True](text)


@always_inline
def matched_bytes[regex: Regex](text: String) -> Int:
    """Sum byte lengths of leftmost, non-overlapping matches."""
    return count_spans[regex](text)


@always_inline
def matched_bytes_span[regex: Regex](text: ImmStringSpan) -> Int:
    """Borrowed-input version of matched_bytes."""
    return count_spans_span[regex](text)


@always_inline
def count[regex: Regex](text: String) -> Int:
    """Count leftmost, non-overlapping matches in `text`."""
    return _count_impl[regex, False](text[byte = 0 : text.byte_length()])


@always_inline
def count_span[regex: Regex](text: ImmStringSpan) -> Int:
    """Borrowed-input version of `count`."""
    return _count_impl[regex, False](text)


@always_inline
def count_captures_span[regex: Regex](text: ImmStringSpan) raises -> Int:
    """Count participating groups in all non-overlapping matches."""
    comptime if _is_anchored_lazy_capture_record[regex]():
        return (
            regex.capture_count
            + 1 if _matches_anchored_lazy_capture_record[regex](text) else 0
        )
    comptime if _is_delimited_capture_record[regex]():
        return (regex.capture_count + 1) if find_span[regex](text) else 0
    comptime if _all_captures_mandatory[regex]():
        return count_span[regex](text) * (regex.capture_count + 1)
    comptime capture_count = _constant_capture_count[regex]()
    comptime if capture_count >= 0:
        return count_span[regex](text) * capture_count
    comptime if _is_delimited_capture_record_with_optional_tail[regex]():
        var record = find_span[regex](text)
        if not record:
            return 0
        return regex.capture_count + Int(
            record.unsafe_value().start(regex.capture_count) >= 0
        )
    comptime if _is_fixed_capture_sequence[regex]():
        var total = 0
        var search_start = 0
        while search_start <= text.byte_length():
            var next = find_span[regex](text, search_start)
            if not next:
                break
            var found = next.unsafe_value()
            total += regex.capture_count + Int(
                found.start(regex.capture_count) >= 0
            )
            search_start = found.end()
        return total

    var total = 0
    var search_start = 0
    while search_start <= text.byte_length():
        var next = _nfa_find_capture_participation[regex](text, search_start)
        if not next:
            break
        var found = next.unsafe_value()
        total += 1
        var groups = found.groups
        while groups != 0:
            groups &= groups - 1
            total += 1
        # Capture-count models guarantee non-empty matches.
        search_start = found.span.end
    return total


@always_inline
def count_captures[regex: Regex](text: String) raises -> Int:
    """Count participating groups in all non-overlapping matches."""
    return count_captures_span[regex](text[byte = 0 : text.byte_length()])


@always_inline
def _grep_search_lines[regex: Regex](text: String) -> Int:
    """Apply Boolean search to each input line, excluding terminal LF."""
    var length = text.byte_length()
    var total = 0
    var bytes = text.as_bytes()
    var line_start = 0
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = length if newline < 0 else newline
        if line_end > line_start and Int(bytes[line_end - 1]) == 13:
            line_end -= 1
        total += Int(search_span[regex](text[byte=line_start:line_end]))
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def _grep_capture_lines[regex: Regex](text: String) raises -> Int:
    """Count capture participation per line, excluding terminal LF."""
    var length = text.byte_length()
    var total = 0
    var bytes = text.as_bytes()
    var line_start = 0
    while line_start < length:
        var newline = text.find("\n", line_start)
        var line_end = length if newline < 0 else newline
        if line_end > line_start and Int(bytes[line_end - 1]) == 13:
            line_end -= 1
        total += count_captures_span[regex](text[byte=line_start:line_end])
        if newline < 0:
            break
        line_start = newline + 1
    return total


@always_inline
def count_matching_lines[regex: Regex](text: String) -> Int:
    """Count input lines containing a match."""
    comptime lazy_literal = _anchored_lazy_literal_plan[
        regex.nodes, regex.root
    ]()
    comptime if lazy_literal:
        var span = text[byte = 0 : text.byte_length()]
        return _count_anchored_lazy_literal_lines[
            regex, lazy_literal.unsafe_value()
        ](span)
    comptime root = regex.nodes[regex.root]
    comptime if _is_prefixed_infix_search[regex.nodes, root]():
        return _grep_prefixed_infix[regex.nodes, root](text)
    return _grep_search_lines[regex](text)


@always_inline
def count_line_captures[regex: Regex](text: String) raises -> Int:
    """Count capture participation after matching each input line."""
    comptime if (
        _all_captures_mandatory[regex]()
        and _is_anchored_prefix_delimited_line[regex.nodes, regex.root]()
    ):
        var span = text[byte = 0 : text.byte_length()]
        return _count_anchored_prefix_delimited_lines[regex](span) * (
            regex.capture_count + 1
        )
    comptime line_prefix = _line_prefix_run_literal_plan[
        regex.nodes, regex.root
    ]()
    comptime if line_prefix and _all_captures_mandatory[regex]():
        var span = text[byte = 0 : text.byte_length()]
        return _count_line_prefix_run_literal[
            regex, line_prefix.unsafe_value()
        ](span) * (regex.capture_count + 1)
    return _grep_capture_lines[regex](text)


@always_inline
def grep[regex: Regex](text: String) -> Int:
    """Compatibility alias for count_matching_lines."""
    return count_matching_lines[regex](text)


@always_inline
def grep_captures[regex: Regex](text: String) raises -> Int:
    """Compatibility alias for count_line_captures."""
    return count_line_captures[regex](text)
