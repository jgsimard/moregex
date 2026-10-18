"""Allocation-free NFA execution with on-demand compile-time programs."""

from std.bit import count_trailing_zeros
from std.utils import StaticTuple

from ._result import (
    _CaptureOffsets,
    _CaptureParticipation,
    _MatchSpan,
)
from ._syntax import Regex
from ._width import _is_start_anchored

from ._nfa_ordered import (
    _nfa_ordered_capture_match,
    _nfa_ordered_capture_participation,
    _nfa_ordered_match,
)
from ._nfa_program import (
    _NFA_ASSERT,
    _NFA_BRACKET,
    _NFA_BYTE,
    _NFA_CLASS,
    _NFAInstruction,
    _compile_program,
    _instruction_accepts,
    _runtime_assertion_matches,
    _NFA_MATCH,
    _NFA_SPLIT,
    _materialize_program,
)


@fieldwise_init
struct _NFABitStates(TrivialRegisterPassable):
    var consuming: UInt64
    var matched: Bool


@always_inline
def _add_closure[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](
    text: ImmStringSpan,
    position: Int,
    initial: Int,
    mut states: StaticTuple[Int, state_count],
    mut count: Int,
    mut seen: StaticTuple[Int, state_count],
    generation: Int,
) -> Bool:
    var stack = StaticTuple[Int, state_count]()
    var stack_count = 1
    stack[0] = initial
    seen[initial] = generation
    var matched = False
    while stack_count > 0:
        stack_count -= 1
        var pc = stack[stack_count]
        var instruction = program[pc]
        if instruction.kind == _NFA_MATCH:
            matched = True
        elif instruction.kind == _NFA_SPLIT:
            if seen[instruction.out2] != generation:
                seen[instruction.out2] = generation
                stack[stack_count] = instruction.out2
                stack_count += 1
            if seen[instruction.out1] != generation:
                seen[instruction.out1] = generation
                stack[stack_count] = instruction.out1
                stack_count += 1
        elif instruction.kind == _NFA_ASSERT:
            if _runtime_assertion_matches(instruction.arg, text, position):
                if seen[instruction.out1] != generation:
                    seen[instruction.out1] = generation
                    stack[stack_count] = instruction.out1
                    stack_count += 1
        else:
            states[count] = pc
            count += 1
    return matched


def _program_has_assertions[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
]() -> Bool:
    comptime for pc in range(state_count):
        comptime if program[pc].kind == _NFA_ASSERT:
            return True
    return False


def _static_epsilon_closure[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](initial: Int) -> _NFABitStates:
    """Build one assertion-free epsilon closure at compile time."""
    var pending = UInt64(1) << UInt64(initial)
    var visited = UInt64(0)
    var consuming = UInt64(0)
    var matched = False
    while pending != 0:
        var pc = Int(count_trailing_zeros(pending))
        var state_bit = UInt64(1) << UInt64(pc)
        pending &= pending - 1
        if visited & state_bit != 0:
            continue
        visited |= state_bit
        var instruction = program[pc]
        if instruction.kind == _NFA_MATCH:
            matched = True
        elif instruction.kind == _NFA_SPLIT:
            pending |= UInt64(1) << UInt64(instruction.out1)
            pending |= UInt64(1) << UInt64(instruction.out2)
        else:
            consuming |= state_bit
    return _NFABitStates(consuming, matched)


def _static_accept_masks[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
]() -> StaticTuple[UInt64, 256]:
    """Map each possible byte to the consuming states that accept it."""
    var result = StaticTuple[UInt64, 256]()
    for value in range(256):
        var accepting = UInt64(0)
        for pc in range(state_count):
            var instruction = program[pc]
            if (
                instruction.kind == _NFA_BYTE
                or instruction.kind == _NFA_CLASS
                or instruction.kind == _NFA_BRACKET
            ) and _instruction_accepts[state_count, program](pc, value):
                accepting |= UInt64(1) << UInt64(pc)
        result[value] = accepting
    return result


def _static_transitions[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
]() -> Tuple[StaticTuple[UInt64, state_count], UInt64]:
    """Build consuming closures and match-reachable state bits together."""
    var closures = StaticTuple[UInt64, state_count]()
    var matches = UInt64(0)
    comptime for pc in range(state_count):
        comptime instruction = program[pc]
        comptime if (
            instruction.kind == _NFA_BYTE
            or instruction.kind == _NFA_CLASS
            or instruction.kind == _NFA_BRACKET
        ):
            comptime closure = _static_epsilon_closure[state_count, program](
                instruction.out1
            )
            closures[pc] = closure.consuming
            comptime if closure.matched:
                matches |= UInt64(1) << UInt64(pc)
    return (closures, matches)


@always_inline
def _nfa_search_static_bits[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unrolled: Bool,
](text: ImmStringSpan, search_start: Int) -> Bool:
    """Run a small assertion-free NFA using compile-time closure tables."""
    comptime start = _static_epsilon_closure[state_count, program](start_pc)
    comptime accept_masks = _static_accept_masks[state_count, program]()
    comptime transition_data = _static_transitions[state_count, program]()
    comptime transitions = transition_data[0]
    comptime transition_matches = transition_data[1]
    if start.matched:
        return True
    var active = start.consuming
    for position in range(search_start, text.byte_length()):
        var pending = active & accept_masks[Int(text.as_bytes()[position])]
        if pending & transition_matches != 0:
            return True
        var following = start.consuming
        comptime if unrolled:
            comptime for pc in range(state_count):
                if pending & (UInt64(1) << UInt64(pc)) != 0:
                    following |= transitions[pc]
        else:
            while pending != 0:
                var pc = Int(count_trailing_zeros(pending))
                pending &= pending - 1
                following |= transitions[pc]
        active = following
    return False


@always_inline
def _epsilon_closure_bits[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](text: ImmStringSpan, position: Int, seed: UInt64) -> _NFABitStates:
    var pending = seed
    var visited = UInt64(0)
    var consuming = UInt64(0)
    var matched = False
    while pending != 0:
        var pc = Int(count_trailing_zeros(pending))
        var state_bit = UInt64(1) << UInt64(pc)
        pending &= pending - 1
        if visited & state_bit != 0:
            continue
        visited |= state_bit
        var instruction = program[pc]
        if instruction.kind == _NFA_MATCH:
            matched = True
        elif instruction.kind == _NFA_SPLIT:
            pending |= UInt64(1) << UInt64(instruction.out1)
            pending |= UInt64(1) << UInt64(instruction.out2)
        elif instruction.kind == _NFA_ASSERT:
            if _runtime_assertion_matches(instruction.arg, text, position):
                pending |= UInt64(1) << UInt64(instruction.out1)
        else:
            consuming |= state_bit
    return _NFABitStates(consuming, matched)


@always_inline
def _nfa_search_bits[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
](text: ImmStringSpan, search_start: Int) -> Bool:
    var start_bit = UInt64(1) << UInt64(start_pc)
    var active = _epsilon_closure_bits[state_count, program](
        text, search_start, start_bit
    )
    if active.matched:
        return True
    for position in range(search_start, text.byte_length()):
        var pending = active.consuming
        var seed = start_bit
        var value = Int(text.as_bytes()[position])
        while pending != 0:
            var pc = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            if _instruction_accepts[state_count, program](pc, value):
                seed |= UInt64(1) << UInt64(program[pc].out1)
        active = _epsilon_closure_bits[state_count, program](
            text, position + 1, seed
        )
        if active.matched:
            return True
    return False


@always_inline
def _nfa_full_static_bits[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
](text: ImmStringSpan) -> Bool:
    """Run an anchored assertion-free Boolean NFA to the input end."""
    comptime start = _static_epsilon_closure[state_count, program](start_pc)
    if text.byte_length() == 0:
        return start.matched
    comptime accept_masks = _static_accept_masks[state_count, program]()
    comptime transition_data = _static_transitions[state_count, program]()
    comptime transitions = transition_data[0]
    comptime transition_matches = transition_data[1]
    var active = start.consuming
    for position in range(text.byte_length()):
        var pending = active & accept_masks[Int(text.as_bytes()[position])]
        if position + 1 == text.byte_length():
            return pending & transition_matches != 0
        var following = UInt64(0)
        while pending != 0:
            var pc = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            following |= transitions[pc]
        if following == 0:
            return False
        active = following
    return False


@always_inline
def _nfa_full_bits[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
](text: ImmStringSpan) -> Bool:
    """Run an anchored Boolean NFA with runtime zero-width assertions."""
    var active = _epsilon_closure_bits[state_count, program](
        text, 0, UInt64(1) << UInt64(start_pc)
    )
    if text.byte_length() == 0:
        return active.matched
    for position in range(text.byte_length()):
        var pending = active.consuming
        var seed = UInt64(0)
        var value = Int(text.as_bytes()[position])
        while pending != 0:
            var pc = Int(count_trailing_zeros(pending))
            pending &= pending - 1
            if _instruction_accepts[state_count, program](pc, value):
                seed |= UInt64(1) << UInt64(program[pc].out1)
        if seed == 0:
            return False
        active = _epsilon_closure_bits[state_count, program](
            text, position + 1, seed
        )
    return active.matched


@always_inline
def _nfa_search_from[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Bool:
    """Search from an input offset with a stack-resident Thompson NFA."""
    comptime compiled = _compile_program(regex.nodes, regex.root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    comptime if state_count <= 64:
        comptime if not _program_has_assertions[state_count, program]():
            return _nfa_search_static_bits[
                state_count, program, start_pc, state_count <= 8
            ](text, search_start)
        else:
            return _nfa_search_bits[state_count, program, start_pc](
                text, search_start
            )
    var current = StaticTuple[Int, state_count]()
    var following = StaticTuple[Int, state_count]()
    var seen = StaticTuple[Int, state_count]()
    var current_count = 0
    var following_count: Int
    var generation = 1
    if _add_closure[state_count, program](
        text,
        search_start,
        start_pc,
        current,
        current_count,
        seen,
        generation,
    ):
        return True

    for position in range(search_start, text.byte_length()):
        generation += 1
        following_count = 0
        var value = Int(text.as_bytes()[position])
        for state in range(current_count):
            var pc = current[state]
            if _instruction_accepts[state_count, program](pc, value):
                if _add_closure[state_count, program](
                    text,
                    position + 1,
                    program[pc].out1,
                    following,
                    following_count,
                    seen,
                    generation,
                ):
                    return True
        if _add_closure[state_count, program](
            text,
            position + 1,
            start_pc,
            following,
            following_count,
            seen,
            generation,
        ):
            return True
        var temporary = current
        current = following
        following = temporary
        current_count = following_count
    return False


@always_inline
def _nfa_find_from[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[_MatchSpan]:
    """Return the ordered leftmost-first match at or after an input offset."""
    comptime compiled = _compile_program(regex.nodes, regex.root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    comptime unanchored = not _is_start_anchored[regex.nodes, regex.root]()
    return _nfa_ordered_match[state_count, program, start_pc, unanchored](
        text, search_start
    )


@always_inline
def _nfa_match_at[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Optional[_MatchSpan]:
    """Try the ordered NFA at one exact byte offset."""
    comptime compiled = _compile_program(regex.nodes, regex.root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    return _nfa_ordered_match[state_count, program, start_pc, False](
        text, start
    )


@always_inline
def _nfa_find_captures[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[
    _CaptureOffsets[regex.capture_count]
]:
    """Return the next match with capture offsets from the preserved AST."""
    comptime compiled = _compile_program(regex.nodes, regex.capture_root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    comptime unanchored = not _is_start_anchored[regex.nodes, regex.root]()
    return _nfa_ordered_capture_match[
        state_count, regex.capture_count, program, start_pc, unanchored
    ](text, search_start)


@always_inline
def _nfa_find_capture_participation[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[_CaptureParticipation]:
    """Return the next match and its capture participation bit mask."""
    comptime compiled = _compile_program(regex.nodes, regex.capture_root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    comptime unanchored = not _is_start_anchored[regex.nodes, regex.root]()
    return _nfa_ordered_capture_participation[
        state_count, program, start_pc, unanchored
    ](text, search_start)


@always_inline
def _nfa_match_captures_at[
    regex: Regex
](text: ImmStringSpan, start: Int) -> Optional[
    _CaptureOffsets[regex.capture_count]
]:
    """Try a capture match at one exact byte offset."""
    comptime compiled = _compile_program(regex.nodes, regex.capture_root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    return _nfa_ordered_capture_match[
        state_count, regex.capture_count, program, start_pc, False
    ](text, start)


@always_inline
def _nfa_full_match[regex: Regex](text: ImmStringSpan) -> Bool:
    """Match the complete input with ordered Thompson-NFA semantics."""
    comptime compiled = _compile_program(regex.nodes, regex.root)
    comptime start_pc = compiled[1]
    comptime state_count = len(compiled[0])
    comptime program = _materialize_program[compiled[0], state_count]()
    # Match priority cannot change a Boolean full-match result. Small NFAs can
    # therefore use one bit per state instead of carrying ordered thread starts.
    comptime if state_count <= 64:
        comptime if not _program_has_assertions[state_count, program]():
            return _nfa_full_static_bits[state_count, program, start_pc](text)
        return _nfa_full_bits[state_count, program, start_pc](text)
    # Large programs retain the ordered executor and an explicit strict-end
    # assertion because their state set does not fit in one machine word.
    comptime strict = _compile_program(regex.nodes, regex.root, True)
    comptime ordered_start_pc = strict[1]
    comptime ordered_state_count = len(strict[0])
    comptime ordered_program = _materialize_program[
        strict[0], ordered_state_count
    ]()
    var result = _nfa_ordered_match[
        ordered_state_count, ordered_program, ordered_start_pc, False
    ](text, 0)
    return Bool(result)


@always_inline
def _nfa_search[regex: Regex](text: ImmStringSpan) -> Bool:
    """Search using a linear-time Thompson NFA."""
    return _nfa_search_from[regex](text, 0)
