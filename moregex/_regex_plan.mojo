"""Shared compile-time execution facts for search and aggregation."""

from ._regex_analysis import (
    _end_anchored_fixed_width,
    _fixed_node_width,
    _has_generic_backtracking_risk,
    _is_end_anchored,
    _is_start_anchored,
    _minimum_node_width,
    _maximum_node_width,
    _required_literal_index,
    _required_one_byte_node_index,
    _simple_class_anchor_item_for_root,
    _simple_infix_literal_item_for_root,
    _start_filter_is_selective,
)
from ._regex_semantics import (
    _nfa_node_supported,
    _nfa_partial_semantics_required,
)
from ._syntax import Regex


@fieldwise_init
struct _RegexExecutionPlan(Copyable, TrivialRegisterPassable):
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
    var requires_ordered_nfa: Bool
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
    return _RegexExecutionPlan(
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
        requires_ordered_nfa,
        nfa_supported,
    )
