"""Compile-time regex syntax tree types and semantic constants."""

from std.builtin.rebind import rebind
from std.builtin.variadics import ParameterList, TypeList, _MLIR
from std.utils import StaticTuple, Variant


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


struct RegexNode(EnumLike, ImplicitlyCopyable):
    """A regex AST node with named cases for exhaustive pattern matching."""

    comptime _Storage = Variant[
        EmptyNode,
        LiteralNode,
        CharClassNode,
        BracketClassNode,
        ZeroWidthNode,
        OrNode,
        RepeatNode,
        SequenceNode,
        CaptureNode,
    ]

    var _value: Self._Storage

    comptime _enum_case_names = ParameterList.of[
        "Empty".value,
        "Literal".value,
        "CharClass".value,
        "BracketClass".value,
        "ZeroWidth".value,
        "Or".value,
        "Repeat".value,
        "Sequence".value,
        "Capture".value,
    ].values
    comptime _enum_case_types: _MLIR.KGENParamListType[AnyType] = TypeList.of[
        Trait=AnyType,
        EmptyNode,
        LiteralNode,
        CharClassNode,
        BracketClassNode,
        ZeroWidthNode,
        OrNode,
        RepeatNode,
        SequenceNode,
        CaptureNode,
    ].values

    @implicit
    def __init__[T: Movable](out self, var value: T):
        self._value = Self._Storage(value^)

    @always_inline
    def isa[T: AnyType](self) -> Bool:
        return self._value.isa[T]()

    @always_inline
    def __getitem_param__[T: AnyType](ref self) -> ref[self] T:
        return Pointer(to=self._value[T]).unsafe_origin_cast[
            origin_of(self)
        ]()[]

    @always_inline
    def _get_enum_discriminant(self) -> Int:
        if self._value.isa[EmptyNode]():
            return 0
        if self._value.isa[LiteralNode]():
            return 1
        if self._value.isa[CharClassNode]():
            return 2
        if self._value.isa[BracketClassNode]():
            return 3
        if self._value.isa[ZeroWidthNode]():
            return 4
        if self._value.isa[OrNode]():
            return 5
        if self._value.isa[RepeatNode]():
            return 6
        if self._value.isa[SequenceNode]():
            return 7
        return 8

    @always_inline
    def _unsafe_get_enum_payload[
        id: Int
    ](ref self) -> ref[self] TypeList[Trait=AnyType, Self._enum_case_types]()[
        id
    ]:
        comptime Payload = TypeList[Trait=AnyType, Self._enum_case_types]()[id]
        return rebind[Payload](
            Pointer(to=self._value.unsafe_get[Payload]()).unsafe_origin_cast[
                origin_of(self)
            ]()[]
        )
