"""Compile-time regex syntax tree types and semantic constants."""

from std.builtin.rebind import rebind
from std.builtin.variadics import TypeList
from std.utils import StaticTuple


comptime MAX_BRANCHES = 64
comptime MAX_SEQUENCE_ITEMS = 32
comptime MAX_CLASS_RANGES = 32
comptime MAX_CAPTURE_GROUPS = 32

comptime CHAR_BYTE_DOT = 0
comptime CHAR_ASCII_WORD = 1
comptime CHAR_ASCII_DIGIT = 2
comptime CHAR_ASCII_WHITESPACE = 3
comptime CHAR_BYTE_DOTALL = 4
comptime CHAR_UNICODE_DOT = 5
comptime CHAR_UNICODE_DOTALL = 6
comptime CHAR_ASCII_NON_WORD = 7
comptime CHAR_ASCII_NON_DIGIT = 8
comptime CHAR_ASCII_NON_WHITESPACE = 9

comptime ASSERT_INPUT_START = 0
comptime ASSERT_INPUT_END = 1
comptime ASSERT_WORD_BOUNDARY = 2
comptime ASSERT_NON_WORD_BOUNDARY = 3
comptime ASSERT_LINE_START = 4
comptime ASSERT_LINE_END = 5


@fieldwise_init
struct EmptyNode(TrivialRegisterPassable):
    pass


@fieldwise_init
struct LiteralNode(ImplicitlyCopyable):
    var value: String


@fieldwise_init
struct CharClassNode(TrivialRegisterPassable):
    var kind: Int


@fieldwise_init
struct BracketClassNode(ImplicitlyCopyable):
    var lows: StaticTuple[Int, MAX_CLASS_RANGES]
    var highs: StaticTuple[Int, MAX_CLASS_RANGES]
    var count: Int
    var negated: Bool


@fieldwise_init
struct ZeroWidthNode(TrivialRegisterPassable):
    var kind: Int


@fieldwise_init
struct OrNode(ImplicitlyCopyable):
    var options: StaticTuple[Int, MAX_BRANCHES]
    var count: Int


@fieldwise_init
struct RepeatNode(TrivialRegisterPassable):
    var child: Int
    var minimum: Int
    # -1 means unbounded.
    var maximum: Int
    var greedy: Bool


@fieldwise_init
struct SequenceNode(ImplicitlyCopyable):
    var items: StaticTuple[Int, MAX_SEQUENCE_ITEMS]
    var count: Int


@fieldwise_init
struct CaptureNode(TrivialRegisterPassable):
    var child: Int
    var index: Int


__enum RegexNode(ImplicitlyCopyable):
    """A regex AST node with named cases for exhaustive pattern matching."""

    case Empty(EmptyNode)
    case Literal(LiteralNode)
    case CharClass(CharClassNode)
    case BracketClass(BracketClassNode)
    case ZeroWidth(ZeroWidthNode)
    case Or(OrNode)
    case Repeat(RepeatNode)
    case Sequence(SequenceNode)
    case Capture(CaptureNode)

    @staticmethod
    def _case_index[T: AnyType]() -> Int:
        """Find a payload type in the compiler-generated case metadata."""
        comptime Cases = TypeList[Trait=AnyType, Self._enum_case_types]
        comptime for i in range(Cases.length):
            comptime if Cases()[i] == Tuple[T]:
                return i
        return -1

    @always_inline
    def isa[T: AnyType](self) -> Bool:
        comptime case_index = Self._case_index[T]()
        comptime assert case_index >= 0, "unsupported regex node payload"
        return self._get_enum_discriminant() == case_index

    @always_inline
    def __getitem_param__[T: AnyType](ref self) -> ref[self] T:
        comptime case_index = Self._case_index[T]()
        comptime assert case_index >= 0, "unsupported regex node payload"
        debug_assert(self.isa[T](), "wrong regex node case")
        return rebind[Tuple[T]](self._unsafe_get_enum_payload[case_index]())[0]
