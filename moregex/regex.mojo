"""Public compile-time-specialized regex API."""

from ._syntax import Regex
from ._execute import (
    _count_impl,
    search,
    search_span,
)
from ._matcher import matches, matches_span
from ._analysis import (
    _anchored_lazy_literal_plan,
    _is_anchored_prefix_delimited_line,
    _line_prefix_run_literal_plan,
)
from ._capture_analysis import (
    _all_captures_mandatory,
    _constant_capture_count,
)
from ._find import (
    _is_anchored_lazy_capture_record,
    _is_delimited_capture_record,
    _is_delimited_capture_record_with_optional_tail,
    _is_fixed_capture_sequence,
    _matches_anchored_lazy_capture_record,
    find_span,
)
from ._nfa import _nfa_find_capture_participation
from ._line_kernels import (
    _count_anchored_lazy_literal_lines,
    _count_anchored_prefix_delimited_lines,
    _count_line_prefix_run_literal,
)
from ._search import _grep_prefixed_infix, _is_prefixed_infix_search


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
