"""Shared compile-time execution facts for search and aggregation."""

from ._analysis import (
    _has_generic_backtracking_risk,
    _required_literal_index,
    _required_one_byte_node_index,
    _simple_class_anchor_item_for_root,
    _simple_infix_literal_item_for_root,
    _start_filter_is_selective,
)
from ._semantics import (
    _nfa_node_supported,
    _nfa_partial_semantics_required,
)
from ._syntax import Regex
from ._width import (
    _end_anchored_fixed_width,
    _fixed_node_width,
    _is_end_anchored,
    _is_start_anchored,
    _maximum_node_width,
    _minimum_node_width,
)


comptime _SEARCH_ORDERED_NFA = 0
comptime _SEARCH_START_ANCHORED = 1
comptime _SEARCH_FIXED_WIDTH = 2
comptime _SEARCH_SIMPLE_INFIX = 3
comptime _SEARCH_SIMPLE_CLASS = 4
comptime _SEARCH_GENERIC = 5

comptime _COUNT_ORDERED_NFA = 0
comptime _COUNT_START_ANCHORED = 1
comptime _COUNT_END_ANCHORED_FIXED = 2
comptime _COUNT_FIXED_WIDTH = 3
comptime _COUNT_SIMPLE_INFIX = 4
comptime _COUNT_SIMPLE_CLASS = 5
comptime _COUNT_GENERIC = 6


@fieldwise_init
struct _RegexExecutionPlan(TrivialRegisterPassable):
    var search_strategy: Int
    var count_strategy: Int
    var minimum_width: Int
    var maximum_width: Int
    var fixed_width: Int
    var required_literal_index: Int
    var required_byte_node_index: Int
    var simple_infix_item: Int
    var simple_class_item: Int
    var end_anchored_width: Int
    var start_anchored: Bool
    var end_anchored: Bool
    var selective_start: Bool
    var backtracking_risk: Bool
    var nfa_supported: Bool

    @always_inline
    def rejects_length(self, length: Int) -> Bool:
        if self.minimum_width > length:
            return True
        if (
            self.start_anchored
            and self.end_anchored
            and self.maximum_width >= 0
        ):
            return length > self.maximum_width + 1
        return False


def _execution_plan[regex: Regex]() -> _RegexExecutionPlan:
    """Analyze dispatch facts once for all public execution modes."""
    comptime minimum = _minimum_node_width[regex.nodes, regex.root]()
    comptime maximum = _maximum_node_width[regex.nodes, regex.root]()
    comptime fixed = _fixed_node_width[regex.nodes, regex.root]()
    comptime required_literal_index = _required_literal_index[
        regex.nodes, regex.root
    ]()
    comptime required_byte = _required_one_byte_node_index[
        regex.nodes, regex.root
    ]()
    comptime simple_infix = _simple_infix_literal_item_for_root[
        regex.nodes, regex.root
    ]()
    comptime simple_class = _simple_class_anchor_item_for_root[
        regex.nodes, regex.root
    ]()
    comptime end_width = _end_anchored_fixed_width[regex.nodes, regex.root]()
    comptime start_anchored = _is_start_anchored[regex.nodes, regex.root]()
    comptime end_anchored = _is_end_anchored[regex.nodes, regex.root]()
    comptime selective = minimum > 0 and _start_filter_is_selective[
        regex.nodes, regex.root
    ]()
    comptime risky = _has_generic_backtracking_risk[regex.nodes, regex.root]()
    comptime requires_ordered_nfa = _nfa_partial_semantics_required(
        regex.nodes, regex.root
    )
    comptime nfa_supported = _nfa_node_supported(regex.nodes, regex.root)
    var search_strategy = _SEARCH_GENERIC
    var count_strategy = _COUNT_GENERIC
    comptime if requires_ordered_nfa:
        search_strategy = _SEARCH_ORDERED_NFA
        count_strategy = _COUNT_ORDERED_NFA
    elif start_anchored:
        search_strategy = _SEARCH_START_ANCHORED
        count_strategy = _COUNT_START_ANCHORED
    else:
        comptime if fixed > 0:
            search_strategy = _SEARCH_FIXED_WIDTH
        elif simple_infix >= 0:
            search_strategy = _SEARCH_SIMPLE_INFIX
        elif simple_class >= 0:
            search_strategy = _SEARCH_SIMPLE_CLASS
        comptime if end_width >= 0:
            count_strategy = _COUNT_END_ANCHORED_FIXED
        elif fixed > 0:
            count_strategy = _COUNT_FIXED_WIDTH
        elif simple_infix >= 0:
            count_strategy = _COUNT_SIMPLE_INFIX
        elif simple_class >= 0:
            count_strategy = _COUNT_SIMPLE_CLASS
    return _RegexExecutionPlan(
        search_strategy,
        count_strategy,
        minimum,
        maximum,
        fixed,
        required_literal_index,
        required_byte,
        simple_infix,
        simple_class,
        end_width,
        start_anchored,
        end_anchored,
        selective,
        risky,
        nfa_supported,
    )
