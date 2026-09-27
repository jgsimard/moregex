"""Byte-run and repeated-class aggregation kernels."""

from ._simd import _consume_simd_width_ladder
from ._ast import (
    CHAR_ASCII_WHITESPACE,
    RepeatNode,
    SequenceNode,
)
from ._syntax import Regex
from std.bit import count_trailing_zeros
from std.memory import pack_bits

from ._common import (
    CLASS_SIMD_WIDTH,
    CLASS_TAIL_SIMD_WIDTH,
    _accepts_class,
    _byte_range_mask,
    _match_checksum,
)

from ._analysis import (
    _bounded_repeat_byte_accepts,
    _fixed_node_mask,
    _one_byte_atom_accepts,
)

from ._byte_scan import (
    _contains_one_byte_node,
    _search_one_byte_run,
)


@always_inline
def _count_one_byte_atom[regex: Regex](text: ImmStringSpan) -> Int:
    """Count accepted one-byte atoms with SIMD mask population reductions."""
    var length = text.byte_length()
    var total = 0
    var offset = 0

    @always_inline
    def scan[
        width: Int
    ](block_start: Int) {imm text, mut total,} -> Bool:
        total += _fixed_node_mask[regex.nodes, regex.root, width, 0](
            text, block_start
        ).reduce_bit_count()
        return False

    _ = _consume_simd_width_ladder(length, offset, scan)

    while offset < length:
        if _one_byte_atom_accepts[regex.nodes, regex.root](
            Int(text.as_bytes()[offset])
        ):
            total += 1
        offset += 1
    return total


@always_inline
def _capitalized_word_phrase_end(text: ImmStringSpan, start: Int) -> Int:
    var length = text.byte_length()
    if start >= length:
        return -1
    var bytes = text.as_bytes()
    var value = Int(bytes[start])
    if not (ord("A") <= value <= ord("Z")):
        return -1
    var end = start + 1
    if end >= length:
        return -1
    value = Int(bytes[end])
    if not (ord("a") <= value <= ord("z")):
        return -1
    end += 1
    while end < length:
        value = Int(bytes[end])
        if not (ord("a") <= value <= ord("z")):
            break
        end += 1
    while end < length and _accepts_class[CHAR_ASCII_WHITESPACE](
        Int(bytes[end])
    ):
        end += 1
    return end


@always_inline
def _next_ascii_uppercase(text: ImmStringSpan, start: Int) -> Int:
    """Find the next ASCII uppercase byte with native-width SIMD."""
    var length = text.byte_length()
    var offset = start
    var pointer = text.unsafe_ptr()
    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while offset + width <= length:
            var values = pointer.unsafe_load[width=width, alignment=1](offset)
            var candidates = _byte_range_mask[ord("A"), ord("Z"), width](values)
            var pending = pack_bits(candidates)
            if pending != 0:
                return offset + Int(count_trailing_zeros(pending))
            offset += width
    var bytes = text.as_bytes()
    while offset < length:
        var value = Int(bytes[offset])
        if ord("A") <= value <= ord("Z"):
            return offset
        offset += 1
    return -1


@always_inline
def _count_bounded_capitalized_word_sequence[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count capitalized phrase runs once instead of retrying nested repeats."""
    comptime outer = regex.nodes[regex.root][RepeatNode]
    comptime minimum = outer.minimum
    comptime maximum = outer.maximum
    var total = 0
    var offset = 0
    var length = text.byte_length()
    while offset < length:
        offset = _next_ascii_uppercase(text, offset)
        if offset < 0:
            break
        var phrase_end = _capitalized_word_phrase_end(text, offset)
        if phrase_end < 0:
            offset += 1
            continue
        var match_start = offset
        var phrases = 0
        while phrase_end >= 0:
            phrases += 1
            offset = phrase_end
            if phrases == maximum:
                total += _match_checksum[sum_spans](offset - match_start)
                phrases = 0
                match_start = offset
            phrase_end = _capitalized_word_phrase_end(text, offset)
        if phrases >= minimum:
            total += _match_checksum[sum_spans](offset - match_start)
    return total


@always_inline
def _bounded_class_run_checksum[
    minimum: Int, maximum: Int, greedy: Bool, sum_spans: Bool
](run_length: Int) -> Int:
    comptime if maximum < 0:
        if run_length < minimum:
            return 0
        comptime if greedy:
            comptime if sum_spans:
                return run_length
            return 1
        else:
            var matches = run_length // minimum
            comptime if sum_spans:
                return matches * minimum
            return matches
    elif greedy:
        var full_matches = run_length // maximum
        var remainder = run_length - full_matches * maximum
        comptime if sum_spans:
            if remainder >= minimum:
                return full_matches * maximum + remainder
            return full_matches * maximum
        else:
            return full_matches + Int(remainder >= minimum)
    else:
        var matches = run_length // minimum
        comptime if sum_spans:
            return matches * minimum
        else:
            return matches


@always_inline
def _count_one_byte_class_repeat[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """SIMD-classify bytes and consume each maximal accepted run once."""
    comptime repeat = regex.nodes[regex.root][RepeatNode]
    comptime minimum = repeat.minimum
    comptime maximum = repeat.maximum
    var length = text.byte_length()
    if length < minimum:
        return 0
    var total = 0
    var run_length = 0
    var offset = 0
    while offset + CLASS_SIMD_WIDTH <= length:
        var accepted = _fixed_node_mask[
            regex.nodes, repeat.child, CLASS_SIMD_WIDTH, 0
        ](text, offset)
        var rejected = pack_bits(
            accepted ^ SIMD[.bool, CLASS_SIMD_WIDTH](fill=True)
        )
        var block_position = 0
        while rejected != 0:
            var lane = Int(count_trailing_zeros(rejected))
            run_length += lane - block_position
            total += _bounded_class_run_checksum[
                minimum, maximum, repeat.greedy, sum_spans
            ](run_length)
            run_length = 0
            block_position = lane + 1
            rejected &= rejected - 1
        run_length += CLASS_SIMD_WIDTH - block_position
        offset += CLASS_SIMD_WIDTH

    var bytes = text.as_bytes()
    while offset < length:
        if _bounded_repeat_byte_accepts[regex.nodes, repeat.child](
            Int(bytes[offset])
        ):
            run_length += 1
        else:
            total += _bounded_class_run_checksum[
                minimum, maximum, repeat.greedy, sum_spans
            ](run_length)
            run_length = 0
        offset += 1
    return total + _bounded_class_run_checksum[
        minimum, maximum, repeat.greedy, sum_spans
    ](run_length)


@always_inline
def _search_one_byte_class_repeat[regex: Regex](text: ImmStringSpan) -> Bool:
    """Search a root byte-predicate repeat by complete runs, not starts."""
    comptime repeat = regex.nodes[regex.root][RepeatNode]
    return _search_one_byte_run[regex.nodes, repeat.child, repeat.minimum](text)


@always_inline
def _count_nested_run_then_disjoint_class[
    regex: Regex, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count `(class+)*other_class` as the equivalent `class*other_class`."""
    comptime sequence = regex.nodes[regex.root][SequenceNode]
    comptime outer = regex.nodes[sequence.items[0]][RepeatNode]
    comptime inner = regex.nodes[outer.child][RepeatNode]
    comptime suffix_index = sequence.items[1]
    if not _contains_one_byte_node[regex.nodes, suffix_index](text):
        return 0

    var total = 0
    var run_length = 0
    var bytes = text.as_bytes()
    for position in range(text.byte_length()):
        var value = Int(bytes[position])
        if _one_byte_atom_accepts[regex.nodes, inner.child](value):
            run_length += 1
        elif _one_byte_atom_accepts[regex.nodes, suffix_index](value):
            total += _match_checksum[sum_spans](run_length + 1)
            run_length = 0
        else:
            run_length = 0
    return total
