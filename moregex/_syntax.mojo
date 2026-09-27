"""Compile-time regex value construction."""

from std.os import abort

from ._ast import LiteralNode, RegexNode
from ._parser import _Parser
from ._normalization import _append_without_captures
from ._nfa_program import _NFAInstruction, _compile_program
from ._semantics import _semantics_supported
from ._width import _semantic_is_start_anchored


struct _CompiledProgram(ImplicitlyCopyable):
    """One materialized NFA program and its entry instruction."""

    var instructions: List[_NFAInstruction]
    var start: Int
    var start_anchored: Bool

    def __init__(out self):
        self.instructions = List[_NFAInstruction]()
        self.start = 0
        self.start_anchored = False

    def __init__(
        out self,
        instructions: List[_NFAInstruction],
        start: Int,
        start_anchored: Bool,
    ):
        self.instructions = instructions.copy()
        self.start = start
        self.start_anchored = start_anchored

    def __init__(out self, *, copy: Self):
        self.instructions = copy.instructions.copy()
        self.start = copy.start
        self.start_anchored = copy.start_anchored

    def __init__(out self, *, deinit move: Self):
        self.instructions = move.instructions^
        self.start = move.start
        self.start_anchored = move.start_anchored


struct Regex(ImplicitlyCopyable):
    """A parsed regex. Use `comptime` so parsing occurs at compile time."""

    var nodes: List[RegexNode]
    var root: Int
    var source: StaticString
    var has_static_source: Bool
    var capture_root: Int
    var capture_count: Int
    var nfa: _CompiledProgram
    var capture_nfa: _CompiledProgram
    var strict_nfa: _CompiledProgram

    def _parse(
        mut self,
        pattern: String,
        case_insensitive: Bool,
        unicode: Bool,
    ):
        var parser = _Parser(pattern, case_insensitive, unicode)
        try:
            var parsed_root = parser.parse()
            self.capture_count = parser.capture_count
            if self.capture_count > 0:
                self.capture_root = parsed_root
                # Preserve capture-bearing nodes as the arena prefix and append
                # the capture-free execution tree into the same allocation.
                var nodes = parser.nodes.copy()
                self.root = _append_without_captures(
                    parser.nodes, parsed_root, nodes
                )
                self.nodes = nodes^
            else:
                self.capture_root = parsed_root
                self.root = parsed_root
                self.nodes = parser.nodes.copy()
            if not _semantics_supported(self.nodes, self.root):
                raise Error(
                    "pattern requires ordered NFA semantics beyond the "
                    "configured compile-time expansion limit"
                )
            var start_anchored = _semantic_is_start_anchored(
                self.nodes, self.root
            )
            var compiled = _compile_program(self.nodes, self.root)
            self.nfa = _CompiledProgram(
                compiled[0], compiled[1], start_anchored
            )
            if self.capture_count > 0:
                var captured = _compile_program(self.nodes, self.capture_root)
                self.capture_nfa = _CompiledProgram(
                    captured[0], captured[1], start_anchored
                )
            if len(self.nfa.instructions) > 64:
                var strict = _compile_program(
                    self.nodes, self.root, strict_end=True
                )
                self.strict_nfa = _CompiledProgram(
                    strict[0], strict[1], start_anchored
                )
        except error:
            abort(String(t"invalid regex '{parser.pattern}': {error}"))

    def __init__(
        out self,
        pattern: String,
        static_source: StaticString,
        has_static_source: Bool,
        case_insensitive: Bool,
        unicode: Bool,
    ):
        self.nodes = List[RegexNode]()
        self.root = 0
        self.source = static_source
        self.has_static_source = has_static_source
        self.capture_root = 0
        self.capture_count = 0
        self.nfa = _CompiledProgram()
        self.capture_nfa = _CompiledProgram()
        self.strict_nfa = _CompiledProgram()
        self._parse(pattern, case_insensitive, unicode)

    def __init__(
        out self,
        pattern: StringLiteral,
        *,
        case_insensitive: Bool = False,
        unicode: Bool = False,
    ):
        self = Self(
            String(pattern),
            StaticString(pattern),
            True,
            case_insensitive,
            unicode,
        )

    def __init__(
        out self,
        pattern: StaticString,
        *,
        case_insensitive: Bool = False,
        unicode: Bool = False,
    ):
        self = Self(
            String(pattern),
            pattern,
            True,
            case_insensitive,
            unicode,
        )

    def __init__(
        out self,
        pattern: String,
        *,
        case_insensitive: Bool = False,
        unicode: Bool = False,
    ):
        self = Self(pattern, "", False, case_insensitive, unicode)

    def __init__(out self, *, copy: Self):
        self.nodes = copy.nodes.copy()
        self.root = copy.root
        self.source = copy.source
        self.has_static_source = copy.has_static_source
        self.capture_root = copy.capture_root
        self.capture_count = copy.capture_count
        self.nfa = copy.nfa
        self.capture_nfa = copy.capture_nfa
        self.strict_nfa = copy.strict_nfa

    def __init__(out self, *, deinit move: Self):
        self.nodes = move.nodes^
        self.root = move.root
        self.source = move.source
        self.has_static_source = move.has_static_source
        self.capture_root = move.capture_root
        self.capture_count = move.capture_count
        self.nfa = move.nfa^
        self.capture_nfa = move.capture_nfa^
        self.strict_nfa = move.strict_nfa^


def _static_source_is_root_literal[regex: Regex]() -> Bool:
    """Return whether the original pattern is the root literal."""
    comptime if not regex.has_static_source:
        return False
    comptime root = regex.nodes[regex.root]
    comptime if not root.isa[LiteralNode]():
        return False
    comptime literal = root[LiteralNode]
    comptime if regex.source.byte_length() != literal.value.byte_length():
        return False
    comptime for i in range(literal.value.byte_length()):
        comptime if regex.source.as_bytes()[i] != literal.value.as_bytes()[i]:
            return False
    return True
