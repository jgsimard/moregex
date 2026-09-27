"""Compile-time regex value construction."""

from std.os import abort

from ._ast import RegexNode
from ._parser import _Parser, _append_without_captures
from ._regex_nfa_program import _NFAInstruction, _compile_program
from ._regex_semantics import _semantics_supported


struct Regex(ImplicitlyCopyable):
    """A parsed regex. Use `comptime` so parsing occurs at compile time."""

    var nodes: List[RegexNode]
    var root: Int
    var source: StaticString
    var has_static_source: Bool
    var capture_root: Int
    var capture_count: Int
    var nfa_program: List[_NFAInstruction]
    var nfa_start: Int
    var capture_program: List[_NFAInstruction]
    var capture_start: Int
    var strict_program: List[_NFAInstruction]
    var strict_start: Int

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
            var compiled = _compile_program(self.nodes, self.root)
            self.nfa_program = compiled[0].copy()
            self.nfa_start = compiled[1]
            if self.capture_count > 0:
                var captured = _compile_program(self.nodes, self.capture_root)
                self.capture_program = captured[0].copy()
                self.capture_start = captured[1]
            if len(self.nfa_program) > 64:
                var strict = _compile_program(
                    self.nodes, self.root, strict_end=True
                )
                self.strict_program = strict[0].copy()
                self.strict_start = strict[1]
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
        self.nfa_program = List[_NFAInstruction]()
        self.nfa_start = 0
        self.capture_program = List[_NFAInstruction]()
        self.capture_start = 0
        self.strict_program = List[_NFAInstruction]()
        self.strict_start = 0
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
        self.nfa_program = copy.nfa_program.copy()
        self.nfa_start = copy.nfa_start
        self.capture_program = copy.capture_program.copy()
        self.capture_start = copy.capture_start
        self.strict_program = copy.strict_program.copy()
        self.strict_start = copy.strict_start

    def __init__(out self, *, deinit move: Self):
        self.nodes = move.nodes^
        self.root = move.root
        self.source = move.source
        self.has_static_source = move.has_static_source
        self.capture_root = move.capture_root
        self.capture_count = move.capture_count
        self.nfa_program = move.nfa_program^
        self.nfa_start = move.nfa_start
        self.capture_program = move.capture_program^
        self.capture_start = move.capture_start
        self.strict_program = move.strict_program^
        self.strict_start = move.strict_start
