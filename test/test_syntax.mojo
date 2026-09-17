from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import Regex, count, count_spans, finditer, matches


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


def test_factored_utf8_byte_class_repetition() raises:
    comptime unbounded = Regex(
        "(?:[A-Z]|[\\xC3][\\x80-\\x96]|[\\xC3][\\x98-\\xB6])+",
        unicode=True,
    )
    assert_equal(count[unbounded]("AÀÖØö!"), 1)
    assert_equal(count_spans[unbounded]("AÀÖØö!"), 9)

    comptime bounded = Regex(
        "(?:[A-Z]|[\\xC3][\\x80-\\x96]|[\\xC3][\\x98-\\xB6]){2,3}",
        unicode=True,
    )
    assert_equal(count[bounded]("AÀÖØö!"), 2)

    comptime infix = Regex(
        (
            "(?:[A-Za-z]|[\\xC3][\\x80-\\xB6])+herloc"
            "(?:[A-Za-z]|[\\xC3][\\x80-\\xB6])+|"
            "(?:[A-Za-z]|[\\xC3][\\x80-\\xB6])+olme"
            "(?:[A-Za-z]|[\\xC3][\\x80-\\xB6])+"
        ),
        unicode=True,
    )
    assert_equal(count_spans[infix]("Holmes and Sherlock"), 14)

    comptime exact_sequence = Regex(
        (
            "(?:[A-Z]|[\\xC3][\\x80-\\x96]){2}[ ]"
            "(?:[A-Z]|[\\xC3][\\x80-\\x96]){1}[ ]"
            "(?:[A-Z]|[\\xC3][\\x80-\\x96]){2}"
        ),
        unicode=True,
    )
    assert_equal(count[exact_sequence]("AÀ B ÖZ! XX Y ZZ"), 2)
    assert_equal(count_spans[exact_sequence]("AÀ B ÖZ! XX Y ZZ"), 16)


def test_bounded_line_gap_normalization() raises:
    comptime gap = Regex("A(?:\\s*.+\\s*){0,2}B|B(?:\\s*.+\\s*){0,2}A")
    var text = "A one\n two B / A one\n two\n three B / B same A"
    var expected = 0
    var found = finditer[gap](text)
    for item in found:
        expected += item.end() - item.start()
    assert_equal(count_spans[gap](text), expected)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
