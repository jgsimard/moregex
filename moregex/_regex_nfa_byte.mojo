"""Shared byte and assertion predicates for NFA executors."""

from std.utils import StaticTuple

from ._regex_common import _runtime_class_accepts, _zero_width_matches
from ._regex_nfa_program import (
    _NFA_BYTE,
    _NFA_CLASS,
    _NFAInstruction,
    _NFA_STRICT_END,
)


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
