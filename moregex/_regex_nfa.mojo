"""Compile-time Thompson NFA construction and allocation-free execution."""

from std.utils import StaticTuple
from std.bit import count_trailing_zeros

from ._ast import (
    CHAR_BYTE_DOTALL,
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
    BracketClassNode,
    CaptureNode,
    CharClassNode,
    EmptyNode,
    LiteralNode,
    OrNode,
    RegexNode,
    RepeatNode,
    SequenceNode,
    ZeroWidthNode,
)
from ._regex_analysis import _is_start_anchored
from ._regex_common import (
    _build_bracket_masks,
    _runtime_class_accepts,
    _zero_width_matches,
)
from ._syntax import Regex


comptime _NFA_MATCH = 0
comptime _NFA_BYTE = 1
comptime _NFA_CLASS = 2
comptime _NFA_BRACKET = 3
comptime _NFA_ASSERT = 4
comptime _NFA_SPLIT = 5
comptime _NFA_CAPTURE_START = 6
comptime _NFA_CAPTURE_END = 7
comptime _NFA_STRICT_END = -1


@fieldwise_init
struct _NFAInstruction(ImplicitlyCopyable, TrivialRegisterPassable):
    var kind: Int
    var out1: Int
    var out2: Int
    var arg: Int
    var mask0: UInt64
    var mask1: UInt64
    var mask2: UInt64
    var mask3: UInt64


@fieldwise_init
struct _NFABitStates(ImplicitlyCopyable, TrivialRegisterPassable):
    var consuming: UInt64
    var matched: Bool


@fieldwise_init
struct _NFAMatch(ImplicitlyCopyable, TrivialRegisterPassable):
    var start: Int
    var consumed: Int


@fieldwise_init
struct _NFACaptureMatch[capture_count: Int](ImplicitlyCopyable):
    var starts: StaticTuple[Int, Self.capture_count + 1]
    var ends: StaticTuple[Int, Self.capture_count + 1]


def _emit_instruction(
    mut program: List[_NFAInstruction],
    kind: Int,
    out1: Int,
    out2: Int,
    arg: Int,
    mask0: UInt64 = 0,
    mask1: UInt64 = 0,
    mask2: UInt64 = 0,
    mask3: UInt64 = 0,
) -> Int:
    var pc = len(program)
    program.append(
        _NFAInstruction(kind, out1, out2, arg, mask0, mask1, mask2, mask3)
    )
    return pc


def _emit_byte_range_instruction(
    mut program: List[_NFAInstruction],
    continuation: Int,
    low: Int,
    high: Int,
    excluded: Int = -1,
) -> Int:
    var masks = StaticTuple[UInt64, 4]()
    for value in range(low, high + 1):
        if value != excluded:
            masks[value // 64] |= UInt64(1) << UInt64(value % 64)
    return _emit_instruction(
        program,
        _NFA_BRACKET,
        continuation,
        -1,
        0,
        masks[0],
        masks[1],
        masks[2],
        masks[3],
    )


def _compile_unicode_dot(
    kind: Int,
    mut program: List[_NFAInstruction],
    continuation: Int,
) -> Int:
    """Compile the staged matcher's 1-4 byte UTF-8 dot semantics."""
    var four = continuation
    for _ in range(3):
        four = _emit_instruction(
            program, _NFA_CLASS, four, -1, CHAR_BYTE_DOTALL
        )
    four = _emit_byte_range_instruction(program, four, 0xF0, 0xF4)

    var three = continuation
    for _ in range(2):
        three = _emit_instruction(
            program, _NFA_CLASS, three, -1, CHAR_BYTE_DOTALL
        )
    three = _emit_byte_range_instruction(program, three, 0xE0, 0xEF)

    var two = _emit_instruction(
        program, _NFA_CLASS, continuation, -1, CHAR_BYTE_DOTALL
    )
    two = _emit_byte_range_instruction(program, two, 0xC2, 0xDF)

    var excluded = ord("\n") if kind == CHAR_UNICODE_DOT else -1
    var one = _emit_byte_range_instruction(
        program, continuation, 0, 0x7F, excluded
    )
    var longer = _emit_instruction(program, _NFA_SPLIT, two, three, 0)
    longer = _emit_instruction(program, _NFA_SPLIT, longer, four, 0)
    return _emit_instruction(program, _NFA_SPLIT, one, longer, 0)


def _compile_node(
    nodes: List[RegexNode],
    node_index: Int,
    mut program: List[_NFAInstruction],
    continuation: Int,
) -> Int:
    ref node = nodes[node_index]
    if node.isa[EmptyNode]():
        return continuation
    if node.isa[LiteralNode]():
        ref literal = node[LiteralNode]
        var start = continuation
        var offset = literal.value.byte_length()
        while offset > 0:
            offset -= 1
            start = _emit_instruction(
                program,
                _NFA_BYTE,
                start,
                -1,
                Int(literal.value.as_bytes()[offset]),
            )
        return start
    if node.isa[CharClassNode]():
        ref char_class = node[CharClassNode]
        if (
            char_class.kind == CHAR_UNICODE_DOT
            or char_class.kind == CHAR_UNICODE_DOTALL
        ):
            return _compile_unicode_dot(char_class.kind, program, continuation)
        return _emit_instruction(
            program, _NFA_CLASS, continuation, -1, char_class.kind
        )
    if node.isa[BracketClassNode]():
        var masks = _build_bracket_masks(node[BracketClassNode])
        return _emit_instruction(
            program,
            _NFA_BRACKET,
            continuation,
            -1,
            0,
            masks[0],
            masks[1],
            masks[2],
            masks[3],
        )
    if node.isa[ZeroWidthNode]():
        return _emit_instruction(
            program, _NFA_ASSERT, continuation, -1, node[ZeroWidthNode].kind
        )
    if node.isa[CaptureNode]():
        ref capture = node[CaptureNode]
        var end = _emit_instruction(
            program, _NFA_CAPTURE_END, continuation, -1, capture.index
        )
        var child = _compile_node(nodes, capture.child, program, end)
        return _emit_instruction(
            program, _NFA_CAPTURE_START, child, -1, capture.index
        )
    if node.isa[OrNode]():
        ref alternation = node[OrNode]
        if alternation.count == 0:
            return continuation
        var option = alternation.count - 1
        var start = _compile_node(
            nodes, alternation.options[option], program, continuation
        )
        while option > 0:
            option -= 1
            var preferred = _compile_node(
                nodes, alternation.options[option], program, continuation
            )
            start = _emit_instruction(program, _NFA_SPLIT, preferred, start, 0)
        return start
    if node.isa[RepeatNode]():
        ref repeat = node[RepeatNode]
        var start = continuation
        if repeat.maximum < 0:
            var split = _emit_instruction(
                program, _NFA_SPLIT, -1, continuation, 0
            )
            var child = _compile_node(nodes, repeat.child, program, split)
            if repeat.greedy:
                program[split].out1 = child
            else:
                program[split].out1 = continuation
                program[split].out2 = child
            start = split
        else:
            var optional_count = repeat.maximum - repeat.minimum
            while optional_count > 0:
                var child = _compile_node(nodes, repeat.child, program, start)
                if repeat.greedy:
                    start = _emit_instruction(
                        program, _NFA_SPLIT, child, start, 0
                    )
                else:
                    start = _emit_instruction(
                        program, _NFA_SPLIT, start, child, 0
                    )
                optional_count -= 1
        var required_count = repeat.minimum
        while required_count > 0:
            start = _compile_node(nodes, repeat.child, program, start)
            required_count -= 1
        return start

    ref sequence = node[SequenceNode]
    var start = continuation
    var item = sequence.count
    while item > 0:
        item -= 1
        start = _compile_node(nodes, sequence.items[item], program, start)
    return start


def _compile_program(
    nodes: List[RegexNode], root: Int, strict_end: Bool = False
) -> Tuple[List[_NFAInstruction], Int]:
    var program = List[_NFAInstruction]()
    var accept = _emit_instruction(program, _NFA_MATCH, -1, -1, 0)
    var continuation = accept
    if strict_end:
        continuation = _emit_instruction(
            program, _NFA_ASSERT, accept, -1, _NFA_STRICT_END
        )
    var start = _compile_node(nodes, root, program, continuation)
    return (program^, start)


def _materialize_program[
    program: List[_NFAInstruction], size: Int
]() -> StaticTuple[_NFAInstruction, size]:
    var result = StaticTuple[_NFAInstruction, size]()
    comptime for i in range(size):
        result[i] = materialize[program[i]]()
    return result


@always_inline
def _runtime_assertion_matches(
    kind: Int, text: ImmStringSpan, position: Int
) -> Bool:
    if kind == _NFA_STRICT_END:
        return position == text.byte_length()
    return _zero_width_matches(kind, text, position)


@always_inline
def _add_ordered_closure[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](
    text: ImmStringSpan,
    position: Int,
    initial: Int,
    thread_start: Int,
    mut states: StaticTuple[Int, state_count],
    mut starts: StaticTuple[Int, state_count],
    mut count: Int,
    mut seen: StaticTuple[Int, state_count],
    generation: Int,
):
    """Append an epsilon closure while preserving split priority."""
    var stack = StaticTuple[Int, 2 * state_count]()
    var stack_count = 1
    stack[0] = initial
    while stack_count > 0:
        stack_count -= 1
        var pc = stack[stack_count]
        if seen[pc] == generation:
            continue
        seen[pc] = generation
        var instruction = program[pc]
        if instruction.kind == _NFA_SPLIT:
            stack[stack_count] = instruction.out2
            stack_count += 1
            stack[stack_count] = instruction.out1
            stack_count += 1
        elif instruction.kind == _NFA_ASSERT:
            if _runtime_assertion_matches(instruction.arg, text, position):
                stack[stack_count] = instruction.out1
                stack_count += 1
        else:
            states[count] = pc
            starts[count] = thread_start
            count += 1


@always_inline
def _nfa_ordered_match[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unanchored: Bool,
](text: ImmStringSpan, search_start: Int) -> Optional[_NFAMatch]:
    """Return the prioritized leftmost-first match of an NFA program."""
    var current = StaticTuple[Int, state_count]()
    var current_starts = StaticTuple[Int, state_count]()
    var following = StaticTuple[Int, state_count]()
    var following_starts = StaticTuple[Int, state_count]()
    var seen = StaticTuple[Int, state_count]()
    for i in range(state_count):
        seen[i] = 0
    var current_count = 0
    var generation = 1
    _add_ordered_closure[state_count, program](
        text,
        search_start,
        start_pc,
        search_start,
        current,
        current_starts,
        current_count,
        seen,
        generation,
    )

    var candidate_start = -1
    var candidate_end = -1
    var position = search_start
    while True:
        var match_index = -1
        for i in range(current_count):
            if program[current[i]].kind == _NFA_MATCH:
                match_index = i
                break
        if match_index >= 0:
            candidate_start = current_starts[match_index]
            candidate_end = position
            current_count = match_index
            if current_count == 0:
                return _NFAMatch(
                    candidate_start, candidate_end - candidate_start
                )

        if position >= text.byte_length():
            if candidate_start >= 0:
                return _NFAMatch(
                    candidate_start, candidate_end - candidate_start
                )
            return None

        generation += 1
        var following_count = 0
        var value = Int(text.as_bytes()[position])
        for i in range(current_count):
            var pc = current[i]
            if _instruction_accepts[state_count, program](pc, value):
                _add_ordered_closure[state_count, program](
                    text,
                    position + 1,
                    program[pc].out1,
                    current_starts[i],
                    following,
                    following_starts,
                    following_count,
                    seen,
                    generation,
                )
        comptime if unanchored:
            if candidate_start < 0:
                _add_ordered_closure[state_count, program](
                    text,
                    position + 1,
                    start_pc,
                    position + 1,
                    following,
                    following_starts,
                    following_count,
                    seen,
                    generation,
                )

        if following_count == 0:
            if candidate_start >= 0:
                return _NFAMatch(
                    candidate_start, candidate_end - candidate_start
                )
            comptime if not unanchored:
                return None
        var temporary = current
        current = following
        following = temporary
        var temporary_starts = current_starts
        current_starts = following_starts
        following_starts = temporary_starts
        current_count = following_count
        position += 1


@always_inline
def _capture_match_result[
    capture_count: Int, slot_count: Int
](
    start: Int,
    end: Int,
    slots: StaticTuple[Int, slot_count],
) -> _NFACaptureMatch[capture_count]:
    var starts = StaticTuple[Int, capture_count + 1]()
    var ends = StaticTuple[Int, capture_count + 1]()
    starts[0] = start
    ends[0] = end
    comptime for group in range(capture_count):
        starts[group + 1] = slots[2 * group]
        ends[group + 1] = slots[2 * group + 1]
    return _NFACaptureMatch(starts, ends)


@always_inline
def _add_ordered_capture_closure[
    state_count: Int,
    slot_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](
    text: ImmStringSpan,
    position: Int,
    initial: Int,
    thread_start: Int,
    initial_slots: StaticTuple[Int, slot_count],
    mut states: StaticTuple[Int, state_count],
    mut starts: StaticTuple[Int, state_count],
    mut slots: StaticTuple[Int, state_count * slot_count],
    mut count: Int,
    mut seen: StaticTuple[Int, state_count],
    generation: Int,
):
    """Append an ordered epsilon closure while carrying capture offsets."""
    var stack = StaticTuple[Int, 2 * state_count]()
    var stack_slots = StaticTuple[Int, 2 * state_count * slot_count]()
    var stack_count = 1
    stack[0] = initial
    comptime for slot in range(slot_count):
        stack_slots[slot] = initial_slots[slot]

    while stack_count > 0:
        stack_count -= 1
        var pc = stack[stack_count]
        if seen[pc] == generation:
            continue
        seen[pc] = generation
        var values = StaticTuple[Int, slot_count]()
        comptime for slot in range(slot_count):
            values[slot] = stack_slots[stack_count * slot_count + slot]
        var instruction = program[pc]
        if instruction.kind == _NFA_SPLIT:
            stack[stack_count] = instruction.out2
            comptime for slot in range(slot_count):
                stack_slots[stack_count * slot_count + slot] = values[slot]
            stack_count += 1
            stack[stack_count] = instruction.out1
            comptime for slot in range(slot_count):
                stack_slots[stack_count * slot_count + slot] = values[slot]
            stack_count += 1
        elif instruction.kind == _NFA_ASSERT:
            if _runtime_assertion_matches(instruction.arg, text, position):
                stack[stack_count] = instruction.out1
                comptime for slot in range(slot_count):
                    stack_slots[stack_count * slot_count + slot] = values[slot]
                stack_count += 1
        elif (
            instruction.kind == _NFA_CAPTURE_START
            or instruction.kind == _NFA_CAPTURE_END
        ):
            var slot = 2 * (instruction.arg - 1)
            if instruction.kind == _NFA_CAPTURE_END:
                slot += 1
            values[slot] = position
            stack[stack_count] = instruction.out1
            comptime for i in range(slot_count):
                stack_slots[stack_count * slot_count + i] = values[i]
            stack_count += 1
        else:
            states[count] = pc
            starts[count] = thread_start
            comptime for slot in range(slot_count):
                slots[count * slot_count + slot] = values[slot]
            count += 1


@always_inline
def _nfa_ordered_capture_match[
    state_count: Int,
    capture_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
    start_pc: Int,
    unanchored: Bool,
](text: ImmStringSpan, search_start: Int) -> Optional[
    _NFACaptureMatch[capture_count]
]:
    """Return a prioritized leftmost-first match and numbered captures."""
    comptime slot_count = 2 * capture_count
    var current = StaticTuple[Int, state_count]()
    var current_starts = StaticTuple[Int, state_count]()
    var current_slots = StaticTuple[Int, state_count * slot_count]()
    var following = StaticTuple[Int, state_count]()
    var following_starts = StaticTuple[Int, state_count]()
    var following_slots = StaticTuple[Int, state_count * slot_count]()
    var seen = StaticTuple[Int, state_count]()
    var empty_slots = StaticTuple[Int, slot_count]()
    var candidate_slots = StaticTuple[Int, slot_count]()
    for i in range(state_count):
        seen[i] = 0
    comptime for slot in range(slot_count):
        empty_slots[slot] = -1
        candidate_slots[slot] = -1

    var current_count = 0
    var generation = 1
    _add_ordered_capture_closure[state_count, slot_count, program](
        text,
        search_start,
        start_pc,
        search_start,
        empty_slots,
        current,
        current_starts,
        current_slots,
        current_count,
        seen,
        generation,
    )

    var candidate_start = -1
    var candidate_end = -1
    var position = search_start
    while True:
        var match_index = -1
        for i in range(current_count):
            if program[current[i]].kind == _NFA_MATCH:
                match_index = i
                break
        if match_index >= 0:
            candidate_start = current_starts[match_index]
            candidate_end = position
            comptime for slot in range(slot_count):
                candidate_slots[slot] = current_slots[
                    match_index * slot_count + slot
                ]
            current_count = match_index
            if current_count == 0:
                return _capture_match_result[capture_count, slot_count](
                    candidate_start, candidate_end, candidate_slots
                )

        if position >= text.byte_length():
            if candidate_start >= 0:
                return _capture_match_result[capture_count, slot_count](
                    candidate_start, candidate_end, candidate_slots
                )
            return None

        generation += 1
        var following_count = 0
        var value = Int(text.as_bytes()[position])
        for i in range(current_count):
            var pc = current[i]
            if _instruction_accepts[state_count, program](pc, value):
                var thread_slots = StaticTuple[Int, slot_count]()
                comptime for slot in range(slot_count):
                    thread_slots[slot] = current_slots[i * slot_count + slot]
                _add_ordered_capture_closure[state_count, slot_count, program](
                    text,
                    position + 1,
                    program[pc].out1,
                    current_starts[i],
                    thread_slots,
                    following,
                    following_starts,
                    following_slots,
                    following_count,
                    seen,
                    generation,
                )
        comptime if unanchored:
            if candidate_start < 0:
                _add_ordered_capture_closure[state_count, slot_count, program](
                    text,
                    position + 1,
                    start_pc,
                    position + 1,
                    empty_slots,
                    following,
                    following_starts,
                    following_slots,
                    following_count,
                    seen,
                    generation,
                )

        if following_count == 0:
            if candidate_start >= 0:
                return _capture_match_result[capture_count, slot_count](
                    candidate_start, candidate_end, candidate_slots
                )
            comptime if not unanchored:
                return None
        var temporary = current
        current = following
        following = temporary
        var temporary_starts = current_starts
        current_starts = following_starts
        following_starts = temporary_starts
        var temporary_slots = current_slots
        current_slots = following_slots
        following_slots = temporary_slots
        current_count = following_count
        position += 1


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


@always_inline
def _instruction_accepts[
    state_count: Int,
    program: StaticTuple[_NFAInstruction, state_count],
](pc: Int, value: Int) -> Bool:
    var instruction = program[pc]
    if instruction.kind == _NFA_BYTE:
        return instruction.arg == value
    if instruction.kind == _NFA_CLASS:
        return _runtime_class_accepts(instruction.arg, value)
    var bit = UInt64(1) << UInt64(value % 64)
    if value < 64:
        return instruction.mask0 & bit != 0
    if value < 128:
        return instruction.mask1 & bit != 0
    if value < 192:
        return instruction.mask2 & bit != 0
    return instruction.mask3 & bit != 0


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
def _nfa_search_from[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Bool:
    """Search from an input offset with a stack-resident Thompson NFA."""
    comptime compiled = _compile_program(regex.nodes, regex.root)
    comptime program_list = compiled[0]
    comptime start_pc = compiled[1]
    comptime state_count = len(program_list)
    comptime program = _materialize_program[program_list, state_count]()
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
](text: ImmStringSpan, search_start: Int) -> Optional[_NFAMatch]:
    """Return the ordered leftmost-first match at or after an input offset."""
    comptime compiled = _compile_program(regex.nodes, regex.root)
    comptime program_list = compiled[0]
    comptime start_pc = compiled[1]
    comptime state_count = len(program_list)
    comptime program = _materialize_program[program_list, state_count]()
    comptime unanchored = not _is_start_anchored[regex.nodes, regex.root]()
    return _nfa_ordered_match[state_count, program, start_pc, unanchored](
        text, search_start
    )


@always_inline
def _nfa_find_captures[
    regex: Regex
](text: ImmStringSpan, search_start: Int) -> Optional[
    _NFACaptureMatch[regex.capture_count]
]:
    """Return the next match with capture offsets from the preserved AST."""
    comptime compiled = _compile_program(
        regex.capture_nodes, regex.capture_root
    )
    comptime program_list = compiled[0]
    comptime start_pc = compiled[1]
    comptime state_count = len(program_list)
    comptime program = _materialize_program[program_list, state_count]()
    comptime unanchored = not _is_start_anchored[regex.nodes, regex.root]()
    return _nfa_ordered_capture_match[
        state_count, regex.capture_count, program, start_pc, unanchored
    ](text, search_start)


@always_inline
def _nfa_full_match[regex: Regex](text: ImmStringSpan) -> Bool:
    """Match the complete input with ordered Thompson-NFA semantics."""
    comptime compiled = _compile_program(regex.nodes, regex.root, True)
    comptime program_list = compiled[0]
    comptime start_pc = compiled[1]
    comptime state_count = len(program_list)
    comptime program = _materialize_program[program_list, state_count]()
    var result = _nfa_ordered_match[state_count, program, start_pc, False](
        text, 0
    )
    return Bool(result)


@always_inline
def _nfa_search[regex: Regex](text: ImmStringSpan) -> Bool:
    """Search using a linear-time Thompson NFA."""
    return _nfa_search_from[regex](text, 0)
