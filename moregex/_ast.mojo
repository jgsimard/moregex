"""Compile-time regex syntax tree types and semantic constants."""

from std.utils import StaticTuple, Variant


comptime MAX_BRANCHES = 64
comptime MAX_SEQUENCE_ITEMS = 32
comptime MAX_CLASS_RANGES = 16

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
struct EmptyNode(ImplicitlyCopyable):
    pass


@fieldwise_init
struct LiteralNode(ImplicitlyCopyable):
    var value: String


@fieldwise_init
struct CharClassNode(ImplicitlyCopyable):
    var kind: Int


@fieldwise_init
struct BracketClassNode(ImplicitlyCopyable):
    var lows: StaticTuple[Int, MAX_CLASS_RANGES]
    var highs: StaticTuple[Int, MAX_CLASS_RANGES]
    var count: Int
    var negated: Bool


@fieldwise_init
struct ZeroWidthNode(ImplicitlyCopyable):
    var kind: Int


@fieldwise_init
struct OrNode(ImplicitlyCopyable):
    var options: StaticTuple[Int, MAX_BRANCHES]
    var count: Int


@fieldwise_init
struct RepeatNode(ImplicitlyCopyable):
    var child: Int
    var minimum: Int
    # -1 means unbounded.
    var maximum: Int
    var greedy: Bool


@fieldwise_init
struct SequenceNode(ImplicitlyCopyable):
    var items: StaticTuple[Int, MAX_SEQUENCE_ITEMS]
    var count: Int


comptime RegexNode = Variant[
    EmptyNode,
    LiteralNode,
    CharClassNode,
    BracketClassNode,
    ZeroWidthNode,
    OrNode,
    RepeatNode,
    SequenceNode,
]
