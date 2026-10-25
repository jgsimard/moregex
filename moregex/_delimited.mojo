"""Direct scans for literal-delimited lazy dot runs, with optional capture."""

from ._ast import (
    CHAR_BYTE_DOT,
    CHAR_BYTE_DOTALL,
    CaptureNode,
    CharClassNode,
    EmptyNode,
    LiteralNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
)
from ._result import _MatchSpan
from ._syntax import Regex


@fieldwise_init
struct _LiteralDelimitedPlan(ImplicitlyCopyable):
    var prefix: String
    var suffix: String
    var dotall: Bool


def _literal_delimited_plan[regex: Regex]() -> Optional[_LiteralDelimitedPlan]:
    """Recognize `literal (.*?) literal` or its capture-free equivalent.

    Join adjacent literal fragments here, including individually escaped braces.
    Only byte dots qualify; Unicode dots must retain code-point validation.
    """
    comptime plan = _analyze_literal_delimited(
        regex.nodes, regex.capture_root, regex.capture_count
    )
    return plan


def _analyze_literal_delimited(
    nodes: List[RegexNode], root_index: Int, capture_count: Int
) -> Optional[_LiteralDelimitedPlan]:
    if capture_count > 1:
        return None
    ref root = nodes[root_index]
    if not root.isa[SequenceNode]():
        return None
    ref sequence = root[SequenceNode]
    var prefix = String()
    var suffix = String()
    var has_body = False
    var dotall = False
    for i in range(sequence.count):
        var index = sequence.items[i]
        ref node = nodes[index]
        if node.isa[EmptyNode]():
            continue
        if node.isa[LiteralNode]():
            if has_body:
                suffix += node[LiteralNode].value
            else:
                prefix += node[LiteralNode].value
            continue
        if has_body:
            return None
        if capture_count == 1:
            if not node.isa[CaptureNode]():
                return None
            ref capture = node[CaptureNode]
            if capture.index != 1:
                return None
            index = capture.child
        ref body = nodes[index]
        if not body.isa[RepeatNode]():
            return None
        ref repeat = body[RepeatNode]
        if repeat.minimum != 0 or repeat.maximum != -1 or repeat.greedy:
            return None
        ref atom = nodes[repeat.child]
        if not atom.isa[CharClassNode]():
            return None
        var kind = atom[CharClassNode].kind
        if kind != CHAR_BYTE_DOT and kind != CHAR_BYTE_DOTALL:
            return None
        dotall = kind == CHAR_BYTE_DOTALL
        has_body = True
    if not has_body or prefix.byte_length() == 0 or suffix.byte_length() == 0:
        return None
    return _LiteralDelimitedPlan(prefix^, suffix^, dotall)


@always_inline
def _find_literal_delimited[
    plan: _LiteralDelimitedPlan
](text: ImmStringSpan, start: Int = 0) -> Optional[_MatchSpan]:
    """Find the first opener and its earliest valid closer without an NFA."""
    var candidate = text.find(plan.prefix, start)
    var suffix_start = -1
    while candidate >= 0:
        var content_start = candidate + plan.prefix.byte_length()
        # Reuse a closer across failed lines rather than rescanning the tail.
        if suffix_start < content_start:
            suffix_start = text.find(plan.suffix, content_start)
        if suffix_start < 0:
            return None
        comptime if not plan.dotall:
            # Limit the scan to this body so repeated matches stay linear.
            var newline = text[byte=content_start:suffix_start].find("\n")
            if newline >= 0:
                # A later opener may itself contain this LF. Retain candidates
                # whose prefix ends after it, including overlapping prefixes.
                var next_start = max(
                    candidate + 1,
                    content_start + newline + 1 - plan.prefix.byte_length(),
                )
                candidate = text.find(plan.prefix, next_start)
                continue
        return _MatchSpan(candidate, suffix_start + plan.suffix.byte_length())
    return None


@always_inline
def _count_literal_delimited[
    plan: _LiteralDelimitedPlan, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    var total = 0
    var start = 0
    while start <= text.byte_length():
        var next = _find_literal_delimited[plan](text, start)
        if not next:
            break
        var found = next.unsafe_value()
        comptime if sum_spans:
            total += found.consumed()
        else:
            total += 1
        start = found.end
    return total


@always_inline
def _matches_literal_delimited[
    plan: _LiteralDelimitedPlan
](text: ImmStringSpan) -> Bool:
    var suffix_start = text.byte_length() - plan.suffix.byte_length()
    if suffix_start < plan.prefix.byte_length():
        return False
    if text[byte = 0 : plan.prefix.byte_length()].find(plan.prefix) != 0:
        return False
    if text.find(plan.suffix, suffix_start) != suffix_start:
        return False
    # Full matching can extend past earlier closers to consume the entire input.
    comptime if not plan.dotall:
        return (
            text[byte = plan.prefix.byte_length() : suffix_start].find("\n") < 0
        )
    return True
