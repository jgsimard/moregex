"""Compile-time regex value construction."""

from std.os import abort

from ._ast import RegexNode
from ._parser import _Parser
from ._regex_semantics import _semantics_supported


struct Regex(ImplicitlyCopyable):
    """A parsed regex. Use `comptime` so parsing occurs at compile time."""

    var nodes: List[RegexNode]
    var root: Int
    var source: StaticString
    var has_static_source: Bool

    def _parse(
        mut self,
        pattern: String,
        case_insensitive: Bool,
        unicode: Bool,
    ):
        var parser = _Parser(pattern, case_insensitive, unicode)
        try:
            self.root = parser.parse()
            if not _semantics_supported(parser.nodes, self.root):
                raise Error(
                    "pattern requires ordered NFA semantics beyond the "
                    "configured compile-time expansion limit"
                )
            self.nodes = parser.nodes.copy()
        except error:
            abort(String(t"invalid regex '{parser.pattern}': {error}"))

    def __init__(
        out self,
        pattern: StringLiteral,
        *,
        case_insensitive: Bool = False,
        unicode: Bool = False,
    ):
        self.nodes = List[RegexNode]()
        self.root = 0
        self.source = StaticString(pattern)
        self.has_static_source = True
        self._parse(String(pattern), case_insensitive, unicode)

    def __init__(
        out self,
        pattern: StaticString,
        *,
        case_insensitive: Bool = False,
        unicode: Bool = False,
    ):
        self.nodes = List[RegexNode]()
        self.root = 0
        self.source = pattern
        self.has_static_source = True
        self._parse(String(pattern), case_insensitive, unicode)

    def __init__(
        out self,
        pattern: String,
        *,
        case_insensitive: Bool = False,
        unicode: Bool = False,
    ):
        self.nodes = List[RegexNode]()
        self.root = 0
        self.source = ""
        self.has_static_source = False
        self._parse(pattern, case_insensitive, unicode)

    def __init__(out self, *, copy: Self):
        self.nodes = copy.nodes.copy()
        self.root = copy.root
        self.source = copy.source
        self.has_static_source = copy.has_static_source

    def __init__(out self, *, deinit move: Self):
        self.nodes = move.nodes^
        self.root = move.root
        self.source = move.source
        self.has_static_source = move.has_static_source
