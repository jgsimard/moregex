"""Specialized literal count kernels."""

from std.bit import count_trailing_zeros
from std.memory import pack_bits

from ._regex_common import (
    CLASS_SIMD_WIDTH,
    CLASS_TAIL_SIMD_WIDTH,
    _match_checksum,
    _match_literal,
)


@always_inline
def _count_static_literal[
    pattern: StaticString, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count a literal while borrowing its original static pattern storage."""
    comptime literal_length = pattern.byte_length()
    var start = text.find(pattern)
    if start < 0:
        return 0
    var total = _match_checksum[sum_spans](literal_length)
    while start + 2 * literal_length <= text.byte_length():
        var next_start = start + literal_length
        start = text.find(pattern, next_start)
        if start < 0:
            break
        total += _match_checksum[sum_spans](literal_length)
    return total


def _literal_has_unique_first_byte[value: String]() -> Bool:
    """Return whether literal matches can never overlap one another."""
    comptime if value.byte_length() < 2:
        return False
    else:
        comptime first = value.as_bytes()[0]
        comptime for i in range(1, value.byte_length()):
            comptime if value.as_bytes()[i] == first:
                return False
        return True


@always_inline
def _matches_short_literal_simd[
    pattern: StaticString
](text: ImmStringSpan, start: Int) -> Bool:
    """Verify a 16--32-byte in-bounds literal with one or two SIMD loads."""
    comptime literal_length = pattern.byte_length()
    comptime width = 16
    var pointer = text.unsafe_ptr()
    var literal_pointer = pattern.as_bytes().unsafe_ptr()
    var first = pointer.unsafe_load[width=width, alignment=1](start)
    var expected_first = literal_pointer.unsafe_load[width=width, alignment=1](
        0
    )
    if not all(first.eq(expected_first)):
        return False
    comptime if literal_length == width:
        return True
    comptime last_start = literal_length - width
    var last = pointer.unsafe_load[width=width, alignment=1](start + last_start)
    var expected_last = literal_pointer.unsafe_load[width=width, alignment=1](
        last_start
    )
    return all(last.eq(expected_last))


@always_inline
def _count_short_literal_simd_candidates[
    pattern: StaticString, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count a small set of unbordered long-literal candidates via SIMD."""
    comptime literal_length = pattern.byte_length()
    comptime first = pattern.as_bytes()[0]
    comptime width = CLASS_TAIL_SIMD_WIDTH
    var candidate_count = text.byte_length() - literal_length + 1
    var pointer = text.unsafe_ptr()
    var total = 0
    var offset = 0
    while offset + width <= candidate_count:
        var values = pointer.unsafe_load[width=width, alignment=1](offset)
        var pending = pack_bits(values.eq(SIMD[.uint8, width](first)))
        while pending != 0:
            var lane = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            if _matches_short_literal_simd[pattern](text, offset + lane):
                total += _match_checksum[sum_spans](literal_length)
        offset += width
    while offset < candidate_count:
        if pointer[
            unsafe_offset=offset
        ] == first and _matches_short_literal_simd[pattern](text, offset):
            total += _match_checksum[sum_spans](literal_length)
        offset += 1
    return total


def _literal_unique_high_byte_offset[value: String]() -> Int:
    """Return a unique non-ASCII byte offset suitable as a SIMD anchor."""
    comptime for position in range(value.byte_length()):
        comptime byte = Int(value.as_bytes()[position])
        comptime if byte >= 0x80:
            var occurrences = 0
            comptime for candidate in range(value.byte_length()):
                comptime if Int(value.as_bytes()[candidate]) == byte:
                    occurrences += 1
            if occurrences == 1:
                return position
    return -1


@always_inline
def _count_unique_anchor_literal[
    value: String, anchor_offset: Int, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count a literal from a unique non-ASCII SIMD anchor byte."""
    comptime literal_length = value.byte_length()
    if text.byte_length() < literal_length:
        return 0
    comptime anchor = value.as_bytes()[anchor_offset]
    var candidate_count = text.byte_length() - literal_length + 1
    var total = 0
    var next_start = 0
    var offset = 0
    var pointer = text.unsafe_ptr()
    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while offset + 2 * width <= candidate_count:
            var first_values = pointer.unsafe_load[width=width, alignment=1](
                offset + anchor_offset
            )
            var second_values = pointer.unsafe_load[width=width, alignment=1](
                offset + width + anchor_offset
            )
            var first_pending = pack_bits(
                first_values.eq(SIMD[.uint8, width](anchor))
            )
            var second_pending = pack_bits(
                second_values.eq(SIMD[.uint8, width](anchor))
            )
            while first_pending != 0:
                var lane = Int(count_trailing_zeros(first_pending))
                first_pending &= first_pending - 1
                var start = offset + lane
                if start >= next_start and _match_literal[value](text, start):
                    total += _match_checksum[sum_spans](literal_length)
                    next_start = start + literal_length
            while second_pending != 0:
                var lane = Int(count_trailing_zeros(second_pending))
                second_pending &= second_pending - 1
                var start = offset + width + lane
                if start >= next_start and _match_literal[value](text, start):
                    total += _match_checksum[sum_spans](literal_length)
                    next_start = start + literal_length
            offset += 2 * width
        while offset + width <= candidate_count:
            var values = pointer.unsafe_load[width=width, alignment=1](
                offset + anchor_offset
            )
            var pending = pack_bits(values.eq(SIMD[.uint8, width](anchor)))
            while pending != 0:
                var lane = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                var start = offset + lane
                if start >= next_start and _match_literal[value](text, start):
                    total += _match_checksum[sum_spans](literal_length)
                    next_start = start + literal_length
            offset += width

    var bytes = text.as_bytes()
    while offset < candidate_count:
        if (
            offset >= next_start
            and bytes[offset + anchor_offset] == anchor
            and _match_literal[value](text, offset)
        ):
            total += _match_checksum[sum_spans](literal_length)
            next_start = offset + literal_length
        offset += 1
    return total


@always_inline
def _count_reverse_unbordered_literal[
    value: String, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """Count non-overlapping literal hits from SIMD first-byte candidates."""
    comptime literal_length = value.byte_length()
    if text.byte_length() < literal_length:
        return 0
    comptime first = value.as_bytes()[0]
    var remaining = text.byte_length() - literal_length + 1
    var total = 0
    var pointer = text.unsafe_ptr()

    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while remaining >= width:
            remaining -= width
            var values = pointer.unsafe_load[width=width, alignment=1](
                remaining
            )
            var pending = pack_bits(values.eq(SIMD[.uint8, width](first)))
            while pending != 0:
                var lane = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                if _match_literal[value](text, remaining + lane):
                    total += _match_checksum[sum_spans](literal_length)

    var bytes = text.as_bytes()
    while remaining > 0:
        remaining -= 1
        if bytes[remaining] == first and _match_literal[value](text, remaining):
            total += _match_checksum[sum_spans](literal_length)
    return total


@always_inline
def _count_edge_prefiltered_literal[
    value: String, sum_spans: Bool
](text: ImmStringSpan) -> Int:
    """SIMD-filter literal starts by their first and last bytes."""
    comptime literal_length = value.byte_length()
    if text.byte_length() < literal_length:
        return 0
    comptime first = value.as_bytes()[0]
    comptime last = value.as_bytes()[literal_length - 1]
    var length = text.byte_length()
    var total = 0
    var next_start = 0
    var offset = 0
    var pointer = text.unsafe_ptr()

    comptime widths = [CLASS_SIMD_WIDTH, CLASS_TAIL_SIMD_WIDTH]
    comptime for width in widths:
        while offset + width + literal_length - 1 <= length:
            var first_values = pointer.unsafe_load[width=width, alignment=1](
                offset
            )
            var last_values = pointer.unsafe_load[width=width, alignment=1](
                offset + literal_length - 1
            )
            var pending = pack_bits(
                first_values.eq(SIMD[.uint8, width](first))
                & last_values.eq(SIMD[.uint8, width](last))
            )
            while pending != 0:
                var lane = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                var start = offset + lane
                if start >= next_start and _match_literal[value](text, start):
                    total += _match_checksum[sum_spans](literal_length)
                    next_start = start + literal_length
            offset += width

    var bytes = text.as_bytes()
    while offset + literal_length <= length:
        if (
            offset >= next_start
            and bytes[offset] == first
            and bytes[offset + literal_length - 1] == last
            and _match_literal[value](text, offset)
        ):
            total += _match_checksum[sum_spans](literal_length)
            next_start = offset + literal_length
        offset += 1
    return total
