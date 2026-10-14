"""Compile-time Thompson NFA program construction."""

from std.utils import StaticTuple

from ._ast import (
    CHAR_BYTE_DOTALL,
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
    RegexNode,
)
from ._byte_predicates import _build_bracket_masks
from ._common import _runtime_class_accepts, _zero_width_matches


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
struct _NFAInstruction(TrivialRegisterPassable):
    var kind: Int
    var out1: Int
    var out2: Int
    var arg: Int
    var mask0: UInt64
    var mask1: UInt64
    var mask2: UInt64
    var mask3: UInt64


@always_inline
def _runtime_assertion_matches(
    kind: Int, text: ImmStringSpan, position: Int
) -> Bool:
    if kind == _NFA_STRICT_END:
        return position == text.byte_length()
    return _zero_width_matches(kind, text, position)


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
    match node:
        case .Empty:
            return continuation
        case .Literal(ref literal):
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
        case .CharClass(ref char_class):
            if (
                char_class.kind == CHAR_UNICODE_DOT
                or char_class.kind == CHAR_UNICODE_DOTALL
            ):
                return _compile_unicode_dot(
                    char_class.kind, program, continuation
                )
            return _emit_instruction(
                program, _NFA_CLASS, continuation, -1, char_class.kind
            )
        case .BracketClass(ref bracket):
            var masks = _build_bracket_masks(bracket)
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
        case .ZeroWidth(ref zero_width):
            return _emit_instruction(
                program, _NFA_ASSERT, continuation, -1, zero_width.kind
            )
        case .Or(ref alternation):
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
                start = _emit_instruction(
                    program, _NFA_SPLIT, preferred, start, 0
                )
            return start
        case .Repeat(ref repeat):
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
                    var child = _compile_node(
                        nodes, repeat.child, program, start
                    )
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
        case .Sequence(ref sequence):
            var start = continuation
            var item = sequence.count
            while item > 0:
                item -= 1
                start = _compile_node(
                    nodes, sequence.items[item], program, start
                )
            return start
        case .Capture(ref capture):
            var end = _emit_instruction(
                program, _NFA_CAPTURE_END, continuation, -1, capture.index
            )
            var child = _compile_node(nodes, capture.child, program, end)
            return _emit_instruction(
                program, _NFA_CAPTURE_START, child, -1, capture.index
            )


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
