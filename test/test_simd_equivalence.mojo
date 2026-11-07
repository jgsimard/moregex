"""Exhaustive scalar/SIMD equivalence checks for every byte class."""

from std.math import iota
from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import Regex, count, count_spans, search

from moregex._ast import (
    CHAR_ASCII_DIGIT,
    CHAR_ASCII_NON_DIGIT,
    CHAR_ASCII_NON_WHITESPACE,
    CHAR_ASCII_NON_WORD,
    CHAR_ASCII_WHITESPACE,
    CHAR_ASCII_WORD,
    CHAR_BYTE_DOT,
    CHAR_BYTE_DOTALL,
    CHAR_UNICODE_DOT,
    CHAR_UNICODE_DOTALL,
)
from moregex._common import CLASS_SIMD_WIDTH, _accepts_class, _class_mask


def check_class[kind: Int]() raises:
    comptime width = 16
    for base in range(0, 256, width):
        var values = iota[DType.uint8, width]() + SIMD[.uint8, width](
            UInt8(base)
        )
        var vector_result = _class_mask[kind, width](values)
        for lane in range(width):
            var value = base + lane
            assert_equal(Bool(vector_result[lane]), _accepts_class[kind](value))


def test_byte_class_simd_equivalence() raises:
    check_class[CHAR_BYTE_DOT]()
    check_class[CHAR_ASCII_WORD]()
    check_class[CHAR_ASCII_DIGIT]()
    check_class[CHAR_ASCII_WHITESPACE]()
    check_class[CHAR_BYTE_DOTALL]()


def test_unicode_class_simd_equivalence() raises:
    check_class[CHAR_UNICODE_DOT]()
    check_class[CHAR_UNICODE_DOTALL]()


def test_complement_class_simd_equivalence() raises:
    check_class[CHAR_ASCII_NON_WORD]()
    check_class[CHAR_ASCII_NON_DIGIT]()
    check_class[CHAR_ASCII_NON_WHITESPACE]()


def test_masked_search_and_unicode_tails() raises:
    comptime email = Regex("([^ @]+)@([^ @]+)")
    comptime dot = Regex(".", unicode=True)
    comptime dotall = Regex("(?s).", unicode=True)
    # Exercise every partial-block length, including UTF-8 codepoints split
    # across full blocks and tails, and delimiter neighbors at the input end.
    for padding in range(2 * CLASS_SIMD_WIDTH + 3):
        var prefix = " " * padding
        assert_true(search[email](prefix + "a@b"))
        assert_false(search[email](prefix + "a@"))
        assert_false(search[email](prefix + "a@ b"))

        var text = "a" * padding + "é\n💩"
        assert_equal(count[dot](text), padding + 2)
        assert_equal(count_spans[dot](text), padding + 6)
        assert_equal(count[dotall](text), padding + 3)
        assert_equal(count_spans[dotall](text), padding + 7)


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
