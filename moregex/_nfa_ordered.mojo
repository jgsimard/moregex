"""Priority-preserving Thompson NFA execution with optional payloads."""

from std.utils import StaticTuple

from ._nfa_program import (
    _NFA_ASSERT,
    _NFA_CAPTURE_END,
    _NFA_CAPTURE_START,
    _NFAInstruction,
    _instruction_accepts,
    _runtime_assertion_matches,
    _NFA_MATCH,
    _NFA_SPLIT,
)
from ._result import (
    _CaptureOffsets,
    _CaptureParticipation,
    _MatchSpan,
)


@fieldwise_init
struct _NFAOrderedResult[slot_count: Int](ImplicitlyCopyable):
    var span: _MatchSpan
    var groups: UInt64
    var slots: StaticTuple[Int, Self.slot_count]


@always_inline
def _add_ordered_closure[
    state_count: Int,
    slot_count: Int,
    track_groups: Bool,
    track_offsets: Bool,
    program: StaticTuple[_NFAInstruction, state_count],
](
    text: ImmStringSpan,
    position: Int,
    initial: Int,
    thread_start: Int,
    initial_groups: UInt64,
    initial_slots: StaticTuple[Int, slot_count],
    mut states: StaticTuple[Int, state_count],
    mut starts: StaticTuple[Int, state_count],
    mut groups: StaticTuple[UInt64, state_count],
    mut slots: StaticTuple[Int, state_count * slot_count],
    mut count: Int,
    mut seen: StaticTuple[Int, state_count],
    generation: Int,
):
    """Append an ordered epsilon closure carrying selected payloads."""
    var stack = StaticTuple[Int, 2 * state_count]()
    var stack_groups = StaticTuple[UInt64, 2 * state_count]()
    var stack_slots = StaticTuple[Int, 2 * state_count * slot_count]()
    var stack_count = 1
    stack[0] = initial
    comptime if track_groups:
        stack_groups[0] = initial_groups
    comptime if track_offsets:
        comptime for slot in range(slot_count):
            stack_slots[slot] = initial_slots[slot]

    while stack_count > 0:
        stack_count -= 1
        var pc = stack[stack_count]
        if seen[pc] == generation:
            continue
        seen[pc] = generation
        var thread_groups = UInt64(0)
        comptime if track_groups:
            thread_groups = stack_groups[stack_count]
        var values = StaticTuple[Int, slot_count]()
        comptime if track_offsets:
            comptime for slot in range(slot_count):
                values[slot] = stack_slots[stack_count * slot_count + slot]

        var instruction = program[pc]
        if instruction.kind == _NFA_SPLIT:
            stack[stack_count] = instruction.out2
            comptime if track_groups:
                stack_groups[stack_count] = thread_groups
            comptime if track_offsets:
                comptime for slot in range(slot_count):
                    stack_slots[stack_count * slot_count + slot] = values[slot]
            stack_count += 1
            stack[stack_count] = instruction.out1
            comptime if track_groups:
                stack_groups[stack_count] = thread_groups
            comptime if track_offsets:
                comptime for slot in range(slot_count):
                    stack_slots[stack_count * slot_count + slot] = values[slot]
            stack_count += 1
        elif instruction.kind == _NFA_ASSERT:
            if _runtime_assertion_matches(instruction.arg, text, position):
                stack[stack_count] = instruction.out1
                comptime if track_groups:
                    stack_groups[stack_count] = thread_groups
                comptime if track_offsets:
                    comptime for slot in range(slot_count):
                        stack_slots[stack_count * slot_count + slot] = values[
                            slot
                        ]
                stack_count += 1
        elif (
            instruction.kind == _NFA_CAPTURE_START
            or instruction.kind == _NFA_CAPTURE_END
        ):
            comptime if track_groups:
                thread_groups |= UInt64(1) << UInt64(instruction.arg - 1)
            comptime if track_offsets:
                var slot = 2 * (instruction.arg - 1)
                if instruction.kind == _NFA_CAPTURE_END:
                    slot += 1
                values[slot] = position
            stack[stack_count] = instruction.out1
            comptime if track_groups:
                stack_groups[stack_count] = thread_groups
            comptime if track_offsets:
                comptime for slot in range(slot_count):
                    stack_slots[stack_count * slot_count + slot] = values[slot]
            stack_count += 1
        else:
            states[count] = pc
            starts[count] = thread_start
            comptime if track_groups:
                groups[count] = thread_groups
            comptime if track_offsets:
                comptime for slot in range(slot_count):
                    slots[count * slot_count + slot] = values[slot]
            count += 1


@always_inline
def _first_match_index[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](states: StaticTuple[Int, state_count], count: Int) -> Int:
    for i in range(count):
        if program[states[i]].kind == _NFA_MATCH:
            return i
    return -1


@always_inline
def _ordered_result[
    slot_count: Int
](
    start: Int,
    end: Int,
    groups: UInt64,
    slots: StaticTuple[Int, slot_count],
) -> _NFAOrderedResult[slot_count]:
    return _NFAOrderedResult(_MatchSpan(start, end), groups, slots)


@always_inline
def _nfa_ordered_execute[
    state_count: Int,
    slot_count: Int,
    track_groups: Bool,
    track_offsets: Bool,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unanchored: Bool,
](text: ImmStringSpan, search_start: Int) -> Optional[
    _NFAOrderedResult[slot_count]
]:
    """Run one prioritized executor with compile-time-selected payloads."""
    var current = StaticTuple[Int, state_count]()
    var current_starts = StaticTuple[Int, state_count]()
    var current_groups = StaticTuple[UInt64, state_count]()
    var current_slots = StaticTuple[Int, state_count * slot_count]()
    var following = StaticTuple[Int, state_count]()
    var following_starts = StaticTuple[Int, state_count]()
    var following_groups = StaticTuple[UInt64, state_count]()
    var following_slots = StaticTuple[Int, state_count * slot_count]()
    var seen = StaticTuple[Int, state_count]()
    var empty_slots = StaticTuple[Int, slot_count]()
    var candidate_slots = StaticTuple[Int, slot_count]()
    for i in range(state_count):
        seen[i] = 0
    comptime if track_offsets:
        comptime for slot in range(slot_count):
            empty_slots[slot] = -1
            candidate_slots[slot] = -1

    var current_count = 0
    var generation = 1
    _add_ordered_closure[
        state_count,
        slot_count,
        track_groups,
        track_offsets,
        program,
    ](
        text,
        search_start,
        start_pc,
        search_start,
        0,
        empty_slots,
        current,
        current_starts,
        current_groups,
        current_slots,
        current_count,
        seen,
        generation,
    )

    var candidate_start = -1
    var candidate_end = -1
    var candidate_groups = UInt64(0)
    var position = search_start
    while True:
        var match_index = _first_match_index[state_count, program](
            current, current_count
        )
        if match_index >= 0:
            candidate_start = current_starts[match_index]
            candidate_end = position
            comptime if track_groups:
                candidate_groups = current_groups[match_index]
            comptime if track_offsets:
                comptime for slot in range(slot_count):
                    candidate_slots[slot] = current_slots[
                        match_index * slot_count + slot
                    ]
            current_count = match_index
            if current_count == 0:
                return _ordered_result(
                    candidate_start,
                    candidate_end,
                    candidate_groups,
                    candidate_slots,
                )

        if position >= text.byte_length():
            if candidate_start >= 0:
                return _ordered_result(
                    candidate_start,
                    candidate_end,
                    candidate_groups,
                    candidate_slots,
                )
            return None

        generation += 1
        var following_count = 0
        var value = Int(text.as_bytes()[position])
        for i in range(current_count):
            var pc = current[i]
            if _instruction_accepts[state_count, program](pc, value):
                var thread_slots = StaticTuple[Int, slot_count]()
                comptime if track_offsets:
                    comptime for slot in range(slot_count):
                        thread_slots[slot] = current_slots[
                            i * slot_count + slot
                        ]
                _add_ordered_closure[
                    state_count,
                    slot_count,
                    track_groups,
                    track_offsets,
                    program,
                ](
                    text,
                    position + 1,
                    program[pc].out1,
                    current_starts[i],
                    current_groups[i],
                    thread_slots,
                    following,
                    following_starts,
                    following_groups,
                    following_slots,
                    following_count,
                    seen,
                    generation,
                )
        comptime if unanchored:
            if candidate_start < 0:
                _add_ordered_closure[
                    state_count,
                    slot_count,
                    track_groups,
                    track_offsets,
                    program,
                ](
                    text,
                    position + 1,
                    start_pc,
                    position + 1,
                    0,
                    empty_slots,
                    following,
                    following_starts,
                    following_groups,
                    following_slots,
                    following_count,
                    seen,
                    generation,
                )

        if following_count == 0:
            if candidate_start >= 0:
                return _ordered_result(
                    candidate_start,
                    candidate_end,
                    candidate_groups,
                    candidate_slots,
                )
            comptime if not unanchored:
                return None
        var temporary = current
        current = following
        following = temporary
        var temporary_starts = current_starts
        current_starts = following_starts
        following_starts = temporary_starts
        comptime if track_groups:
            var temporary_groups = current_groups
            current_groups = following_groups
            following_groups = temporary_groups
        comptime if track_offsets:
            var temporary_slots = current_slots
            current_slots = following_slots
            following_slots = temporary_slots
        current_count = following_count
        position += 1


@always_inline
def _nfa_ordered_match[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unanchored: Bool,
](text: ImmStringSpan, search_start: Int) -> Optional[_MatchSpan]:
    var result = _nfa_ordered_execute[
        state_count, 1, False, False, program, start_pc, unanchored
    ](text, search_start)
    return result.unsafe_value().span if result else None


@always_inline
def _nfa_ordered_capture_participation[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unanchored: Bool,
](text: ImmStringSpan, search_start: Int) -> Optional[_CaptureParticipation]:
    var result = _nfa_ordered_execute[
        state_count, 1, True, False, program, start_pc, unanchored
    ](text, search_start)
    if not result:
        return None
    var found = result.unsafe_value()
    return _CaptureParticipation(found.span, found.groups)


@always_inline
def _nfa_ordered_capture_match[
    state_count: Int,
    capture_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unanchored: Bool,
](text: ImmStringSpan, search_start: Int) -> Optional[
    _CaptureOffsets[capture_count]
]:
    comptime assert capture_count > 0
    comptime slot_count = 2 * capture_count
    var result = _nfa_ordered_execute[
        state_count,
        slot_count,
        False,
        True,
        program,
        start_pc,
        unanchored,
    ](text, search_start)
    if not result:
        return None
    var found = result.unsafe_value()
    var starts = StaticTuple[Int, capture_count + 1]()
    var ends = StaticTuple[Int, capture_count + 1]()
    starts[0] = found.span.start
    ends[0] = found.span.end
    comptime for group in range(capture_count):
        starts[group + 1] = found.slots[2 * group]
        ends[group + 1] = found.slots[2 * group + 1]
    return _CaptureOffsets(starts, ends)
