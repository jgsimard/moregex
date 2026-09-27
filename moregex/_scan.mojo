"""Neutral scanning primitives shared by search and aggregation."""

from ._simd import _consume_simd_width_ladder
from std.bit import count_trailing_zeros
from std.memory import pack_bits

from ._ast import LiteralNode, RegexNode
from ._analysis import (
    _node_start_accepts,
    _node_start_mask,
)
from ._common import (
    _match_checksum,
)
from ._ast_matcher import _match_node
from ._nfa import _nfa_search_from
from ._plan import _execution_plan
from ._syntax import Regex

from ._byte_scan import _contains_one_byte_node


@always_inline
def _scan_generic[
    regex: Regex, sum_spans: Bool, stop_after_first: Bool
](text: ImmStringSpan) -> Int:
    """Run the shared filtered candidate scan for search and aggregation."""
    comptime plan = _execution_plan[regex]()
    comptime if plan.required_literal_index >= 0:
        comptime literal = regex.nodes[plan.required_literal_index]
        comptime if (
            not plan.selective_start
            or literal[LiteralNode].value.byte_length() == 1
        ):
            if text.find(literal[LiteralNode].value) < 0:
                return 0
    comptime if (
        plan.required_literal_index < 0
        and plan.backtracking_risk
        and plan.required_byte_node_index >= 0
    ):
        if not _contains_one_byte_node[
            regex.nodes, plan.required_byte_node_index
        ](text):
            return 0
    comptime if (
        plan.minimum_width > 0
        and plan.required_literal_index < 0
        and plan.backtracking_risk
        and plan.nfa_supported
    ):
        comptime if stop_after_first:
            var probe_end = min(1, text.byte_length() - plan.minimum_width + 1)
            for start in range(probe_end):
                if _match_node[regex.nodes, regex.root](text, start):
                    return 1
            return Int(_nfa_search_from[regex](text, probe_end))
        else:
            var first = _match_node[regex.nodes, regex.root](text, 0)
            if not first and not _nfa_search_from[regex](text, 1):
                return 0

    var total = 0
    var next_start = 0
    var end = text.byte_length() - plan.minimum_width + 1
    comptime if plan.selective_start:

        @always_inline
        def scan[
            width: Int
        ](block_start: Int) {imm text, mut total, mut next_start} -> Bool:
            var values = text.unsafe_ptr().unsafe_load[
                width=width, alignment=1
            ](block_start)
            var pending = pack_bits(
                _node_start_mask[regex.nodes, regex.root, width](values)
            )
            while pending != 0:
                var lane = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                var candidate = block_start + lane
                if candidate < next_start:
                    continue
                var result = _match_node[regex.nodes, regex.root](
                    text, candidate
                )
                if result:
                    comptime if stop_after_first:
                        return True
                    else:
                        var consumed = result.unsafe_value().consumed()
                        total += _match_checksum[sum_spans](consumed)
                        next_start = candidate + max(1, consumed)
            return False

        var offset = 0
        if _consume_simd_width_ladder(end, offset, scan):
            return 1
        while offset < end:
            if offset >= next_start and _node_start_accepts[
                regex.nodes, regex.root
            ](Int(text.as_bytes()[offset])):
                var result = _match_node[regex.nodes, regex.root](text, offset)
                if result:
                    comptime if stop_after_first:
                        return 1
                    else:
                        var consumed = result.unsafe_value().consumed()
                        total += _match_checksum[sum_spans](consumed)
                        next_start = offset + max(1, consumed)
            offset += 1
    else:
        while next_start < end:
            var result = _match_node[regex.nodes, regex.root](text, next_start)
            if result:
                comptime if stop_after_first:
                    return 1
                else:
                    var consumed = result.unsafe_value().consumed()
                    total += _match_checksum[sum_spans](consumed)
                    next_start += max(1, consumed)
            else:
                next_start += 1
    return total
