from std.testing import TestSuite, assert_false, assert_true

from moregex import Regex, matches


def test_wildcards_and_classes() raises:
    comptime wildcard = Regex("a.c")
    assert_true(matches[wildcard]("abc"))
    assert_true(matches[wildcard]("a c"))
    assert_false(matches[wildcard]("ac"))

    comptime classes = Regex("\\w+\\s\\d+")
    assert_true(matches[classes]("abc_9 123"))
    assert_true(matches[classes]("Z\t0"))
    assert_false(matches[classes]("hyphen- 12"))


def test_simd_class_runs() raises:
    # Root class runs use the SIMD full-match path and must retain scalar
    # semantics for short inputs, invalid bytes, and empty strings.
    comptime digits = Regex("\\d+")
    assert_true(matches[digits]("12345678901234567890123456789012"))
    assert_false(matches[digits]("123456789012345x7890123456789012"))
    assert_true(
        matches[digits](
            "1234567890123456789012345678901234567890123456789012345678901234"
        )
    )
    assert_false(
        matches[digits](
            "123456789012345678901234567890123456789012345678901234567890123x"
        )
    )
    assert_false(matches[digits](""))

    comptime words = Regex("\\w+")
    assert_true(matches[words]("long_ascii_word_1234567890"))
    assert_false(matches[words]("long-ascii-word"))


def test_alternatives_and_repetitions() raises:
    comptime alternatives = Regex("cat|dog|fox")
    assert_true(matches[alternatives]("cat"))
    assert_true(matches[alternatives]("dog"))
    assert_true(matches[alternatives]("fox"))
    assert_false(matches[alternatives]("cow"))

    comptime repeats = Regex("ab*c+d?")
    assert_true(matches[repeats]("ac"))
    assert_true(matches[repeats]("abbbcccd"))
    assert_true(matches[repeats]("abbbccc"))
    assert_false(matches[repeats]("ab"))

    comptime grouped = Regex("(ab|cd)+!")
    assert_true(matches[grouped]("ab!"))
    assert_true(matches[grouped]("cdab!"))
    assert_false(matches[grouped]("!"))

    comptime empty_branch = Regex("(|x)")
    assert_true(matches[empty_branch](""))
    assert_true(matches[empty_branch]("x"))


def test_continuation_backtracking() raises:
    # Full matching retries ordered alternatives and nested variable-width
    # repetitions when their continuation cannot complete.
    comptime reconsider = Regex("(a|aa)c")
    assert_true(matches[reconsider]("ac"))
    assert_true(matches[reconsider]("aac"))
    comptime repeated_alternative = Regex("(a|ab)+")
    assert_true(matches[repeated_alternative]("ab"))
    comptime nested_giveback = Regex("(a+)*ab")
    assert_true(matches[nested_giveback]("aaab"))


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
