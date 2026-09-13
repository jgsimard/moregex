"""Match-span, capture, and iteration APIs."""

from std.utils import StaticTuple

from ._ast import EmptyNode, LiteralNode, SequenceNode, ZeroWidthNode
from ._regex_nfa import _nfa_find_captures, _nfa_find_from
from ._syntax import Regex


@fieldwise_init
struct RegexMatch[capture_count: Int](ImplicitlyCopyable):
    """Byte offsets for a full match and its numbered capture groups."""

    var _starts: StaticTuple[Int, Self.capture_count + 1]
    var _ends: StaticTuple[Int, Self.capture_count + 1]

    @always_inline
    def group_count(self) -> Int:
        return Self.capture_count

    @always_inline
    def _check_group(self, group: Int) raises:
        if group < 0 or group > Self.capture_count:
            raise Error(
                String(
                    t"capture group {group} is outside 0..{Self.capture_count}"
                )
            )

    @always_inline
    def start(self, group: Int = 0) raises -> Int:
        """Return a group's byte start, or -1 when it did not participate."""
        self._check_group(group)
        return self._starts[group]

    @always_inline
    def end(self, group: Int = 0) raises -> Int:
        """Return a group's byte end, or -1 when it did not participate."""
        self._check_group(group)
        return self._ends[group]

    @always_inline
    def span(self, group: Int = 0) raises -> Tuple[Int, Int]:
        """Return a group's half-open byte range."""
        self._check_group(group)
        return (self._starts[group], self._ends[group])

    def group(self, text: String, group: Int = 0) raises -> String:
        """Copy a captured substring from the original input."""
        self._check_group(group)
        var start = self._starts[group]
        var end = self._ends[group]
        if start < 0:
            raise Error(String(t"capture group {group} did not participate"))
        return String(text[byte=start:end])

    def group_optional(
        self, text: String, group: Int = 0
    ) raises -> Optional[String]:
        """Return a captured substring, or None for an unmatched group."""
        self._check_group(group)
        var start = self._starts[group]
        if start < 0:
            return None
        return String(text[byte = start : self._ends[group]])


@always_inline
def _prefilter_start[regex: Regex](text: ImmStringSpan, start: Int) -> Int:
    """Skip directly to a required literal at the match's leading edge."""
    comptime root = regex.nodes[regex.root]
    comptime if root.isa[LiteralNode]():
        return text.find(root[LiteralNode].value, start)
    comptime if root.isa[SequenceNode]():
        comptime sequence = root[SequenceNode]
        comptime for i in range(sequence.count):
            comptime item = regex.nodes[sequence.items[i]]
            comptime if item.isa[EmptyNode]() or item.isa[ZeroWidthNode]():
                continue
            comptime if item.isa[LiteralNode]():
                return text.find(item[LiteralNode].value, start)
            return start
    return start


@always_inline
def find_span[
    regex: Regex
](text: ImmStringSpan, start: Int = 0) -> Optional[
    RegexMatch[regex.capture_count]
]:
    """Find the next leftmost-first match at or after a byte offset."""
    var search_start = max(0, start)
    if search_start > text.byte_length():
        return None
    search_start = _prefilter_start[regex](text, search_start)
    if search_start < 0:
        return None
    comptime if regex.capture_count > 0:
        var captured = _nfa_find_captures[regex](text, search_start)
        if not captured:
            return None
        var result = captured.unsafe_value()
        return RegexMatch[regex.capture_count](result.starts, result.ends)
    else:
        var found = _nfa_find_from[regex](text, search_start)
        if not found:
            return None
        var result = found.unsafe_value()
        var starts = StaticTuple[Int, regex.capture_count + 1]()
        var ends = StaticTuple[Int, regex.capture_count + 1]()
        starts[0] = result.start
        ends[0] = result.start + result.consumed
        return RegexMatch[regex.capture_count](starts, ends)


@always_inline
def find[
    regex: Regex
](text: String, start: Int = 0) -> Optional[RegexMatch[regex.capture_count]]:
    """Owned-string convenience wrapper for `find_span`."""
    return find_span[regex](text[byte = 0 : text.byte_length()], start)


def finditer_span[
    regex: Regex
](text: ImmStringSpan) -> List[RegexMatch[regex.capture_count]]:
    """Collect leftmost, non-overlapping matches over a borrowed input."""
    var matches = List[RegexMatch[regex.capture_count]]()
    var search_start = 0
    while search_start <= text.byte_length():
        var next = find_span[regex](text, search_start)
        if not next:
            break
        var found = next.unsafe_value()
        matches.append(found)
        var end = found._ends[0]
        if end > found._starts[0]:
            search_start = end
        else:
            search_start = end + 1
    return matches^


def finditer[
    regex: Regex
](text: String) -> List[RegexMatch[regex.capture_count]]:
    """Collect leftmost, non-overlapping matches over an owned string."""
    return finditer_span[regex](text[byte = 0 : text.byte_length()])
