"""Shared SIMD widths and width-ladder traversal."""

from std.sys import simd_width_of
from std.collections.string.string_span import _get_kgen_string

comptime CLASS_SIMD_WIDTH = simd_width_of[DType.uint8]()
comptime CLASS_TAIL_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 2)
comptime CLASS_QUARTER_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 4)
comptime CLASS_EIGHTH_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 8)
comptime CLASS_SIXTEENTH_SIMD_WIDTH = max(1, CLASS_SIMD_WIDTH // 16)


@inline(.always)
def _masked_load_bytes[
    width: Int
](pointer: ImmPointer[UInt8, _], mask: SIMD[.bool, width]) -> SIMD[
    .uint8, width
]:
    """Load active byte lanes and fill inactive lanes with zero."""
    comptime if width == 1:
        return pointer.unsafe_load() if mask[0] else UInt8(0)
    else:
        # Mojo 1.3 can merge the stdlib intrinsic's argument pack across
        # control flow, hiding the constant alignment from LLVM lowering.
        # Separate operands keep alignment constant while retaining masked
        # memory access for tails that end at the input boundary.
        comptime intrinsic = _get_kgen_string["llvm.masked.load"]()
        return __mlir_op.`pop.call_llvm_intrinsic`[
            intrin=intrinsic,
            _type=SIMD[.uint8, width],
            hasSideEffects=True.__mlir_i1__(),
        ](
            pointer.unsafe_bitcast[NoneType](),
            Int32(1),
            mask,
            SIMD[.uint8, width](0),
        )


@inline(.always)
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


@inline(.always)
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
