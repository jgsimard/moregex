"""Compile-time regex value construction."""

from std.os import abort

from ._ast import RegexNode
from ._parser import _Parser, _append_without_captures
from ._regex_semantics import _semantics_supported


struct Regex(ImplicitlyCopyable):
    """A parsed regex. Use `comptime` so parsing occurs at compile time."""

    var nodes: List[RegexNode]
    var root: Int
    var source: StaticString
    var has_static_source: Bool
    var capture_nodes: List[RegexNode]
    var capture_root: Int
    var capture_count: Int

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
                self.capture_nodes = parser.nodes.copy()
                var nodes = List[RegexNode]()
                self.root = _append_without_captures(
                    parser.nodes, parsed_root, nodes
                )
                self.nodes = nodes^
            else:
                self.capture_root = 0
                self.capture_nodes = List[RegexNode]()
                self.root = parsed_root
                self.nodes = parser.nodes.copy()
            if not _semantics_supported(self.nodes, self.root):
                raise Error(
                    "pattern requires ordered NFA semantics beyond the "
                    "configured compile-time expansion limit"
                )
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
        self.capture_nodes = List[RegexNode]()
        self.capture_root = 0
        self.capture_count = 0
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
        self.capture_nodes = List[RegexNode]()
        self.capture_root = 0
        self.capture_count = 0
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
        self.capture_nodes = List[RegexNode]()
        self.capture_root = 0
        self.capture_count = 0
        self._parse(pattern, case_insensitive, unicode)

    def __init__(out self, *, copy: Self):
        self.nodes = copy.nodes.copy()
        self.root = copy.root
        self.source = copy.source
        self.has_static_source = copy.has_static_source
        self.capture_nodes = copy.capture_nodes.copy()
        self.capture_root = copy.capture_root
        self.capture_count = copy.capture_count

    def __init__(out self, *, deinit move: Self):
        self.nodes = move.nodes^
        self.root = move.root
        self.source = move.source
        self.has_static_source = move.has_static_source
        self.capture_nodes = move.capture_nodes^
        self.capture_root = move.capture_root
        self.capture_count = move.capture_count
