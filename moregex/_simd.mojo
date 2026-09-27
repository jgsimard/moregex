"""Shared SIMD widths and width-ladder traversal."""

from std.sys import simd_width_of

comptime CLASS_SIMD_WIDTH = simd_width_of[DType.uint8]()
comptime CLASS_TAIL_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 2)
comptime CLASS_QUARTER_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 4)
comptime CLASS_EIGHTH_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 8)
comptime CLASS_SIXTEENTH_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 16)


@always_inline
def _search_simd_width_ladder(
    candidate_count: Int,
    base: Int,
    scanner: Some[def[width: Int](start: Int, end: Int) -> Bool],
) -> Bool:
    """Search candidates with native-to-sixteenth-width SIMD blocks."""
    var scanned = 0
    comptime widths = [
        CLASS_SIMD_WIDTH,
        CLASS_TAIL_SIMD_WIDTH,
        CLASS_QUARTER_SIMD_WIDTH,
        CLASS_EIGHTH_SIMD_WIDTH,
        CLASS_SIXTEENTH_SIMD_WIDTH,
    ]
    comptime for width in widths:
        if candidate_count >= width:
            while scanned + width <= candidate_count:
                if scanner[width](base + scanned, 0):
                    return True
                scanned += width
            if scanned < candidate_count:
                if candidate_count - scanned >= CLASS_SIXTEENTH_SIMD_WIDTH:
                    return scanner[width](base + candidate_count - width, 0)
                return scanner[0](base + scanned, base + candidate_count)
            return False

    return scanner[0](base, base + candidate_count)


@always_inline
def _consume_simd_width_ladder(
    limit: Int,
    mut offset: Int,
    scanner: Some[def[width: Int](offset: Int) -> Bool],
) -> Bool:
    """Consume complete SIMD blocks and leave the scalar-tail offset."""
    comptime widths = [
        CLASS_SIMD_WIDTH,
        CLASS_TAIL_SIMD_WIDTH,
        CLASS_QUARTER_SIMD_WIDTH,
        CLASS_EIGHTH_SIMD_WIDTH,
    ]
    comptime for width in widths:
        while offset + width <= limit:
            if scanner[width](offset):
                return True
            offset += width
    return False
