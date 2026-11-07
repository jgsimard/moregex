"""Equivalence tests for generic fallback execution plans."""

from std.testing import TestSuite, assert_equal

from moregex import Regex, matches
from moregex._common import CLASS_SIMD_WIDTH, _match_checksum
from moregex._matcher import _match_node
from moregex._execute import _count_planned, _search_planned
from moregex._nfa import _nfa_full_match, _nfa_match_at


def reference_count[regex: Regex, sum_spans: Bool](text: StringSpan) -> Int:
    """Count with the original match-at-every-position fallback algorithm."""
    var total = 0
    var start = 0
    while start <= text.byte_length():
        var result = _match_node[regex.nodes, regex.root](text, start)
        if result:
            var consumed = result.unsafe_value().consumed()
            total += _match_checksum[sum_spans](consumed)
            start += max(1, consumed)
        else:
            start += 1
    return total


def reference_search[regex: Regex](text: StringSpan) -> Bool:
    for start in range(text.byte_length() + 1):
        if _match_node[regex.nodes, regex.root](text, start):
            return True
    return False


def assert_fallback_equivalent[regex: Regex](text: String) raises:
    var span = text[byte = 0 : text.byte_length()]
    var expected_count = reference_count[regex, False](span)
    var expected_spans = reference_count[regex, True](span)
    assert_equal(_search_planned[regex](span), reference_search[regex](span))
    assert_equal(_count_planned[regex, False](span), expected_count)
    assert_equal(_count_planned[regex, True](span), expected_spans)


def test_delimited_fallback_equivalence() raises:
    comptime email = Regex("[\\w\\.+-]+@[\\w\\.-]+\\.[\\w\\.-]+")
    assert_fallback_equivalent[email](
        "bad@ no person@example.com and foo.bar+tag@example-domain.com!"
    )
    assert_fallback_equivalent[email]("no valid address here")

    comptime delimited = Regex("pre[a-z]+mid[0-9]+post")
    assert_fallback_equivalent[delimited](
        "xx preabmid12post yy prexmid3post zz"
    )
    assert_fallback_equivalent[delimited]("premid12post preabmidpost")

    comptime bounded = Regex("[a-z]{2,4}--[0-9]{1,3}END")
    assert_fallback_equivalent[bounded](
        "x ab--12END y abcde--1END z wxyz--999END"
    )

    comptime multiline = Regex("(?m)^[a-z]+:[0-9]+$")
    assert_fallback_equivalent[multiline]("aa:12\nbad:x\nz:9")

    comptime lazy = Regex("[a-z]+?@[a-z]+?\\.[a-z]+")
    assert_fallback_equivalent[lazy]("xx aa@bb.cc yy d@e.ff")

    comptime repeated_literals = Regex("[a-z]+foo[a-z]+bar[a-z]+")
    assert_fallback_equivalent[repeated_literals]("xxfooqqbarzz 1 afooobarz")

    comptime casefolded = Regex("(?i)[a-f]+:cat:[0-9]+")
    assert_fallback_equivalent[casefolded]("__AbCd:CAT:123__ bad:dog:2")


def test_class_fallback_equivalence() raises:
    comptime broad_class = Regex(".+[A-Z]")
    assert_fallback_equivalent[broad_class]("a" * 256)
    assert_fallback_equivalent[broad_class]("a" * 255 + "Z")
    assert_fallback_equivalent[broad_class]("Z" + "a" * 255)
    assert_fallback_equivalent[broad_class]("aaaZ bbbQ ccc")

    comptime required_classes = Regex("[a-z]+[A-Z][0-9]+")
    assert_fallback_equivalent[required_classes]("letters-only")
    assert_fallback_equivalent[required_classes]("abcZ123")
    assert_fallback_equivalent[required_classes]("Zabc123")

    comptime input_anchored = Regex("^[a-z]+END")
    assert_fallback_equivalent[input_anchored]("a" * 256 + "END")
    assert_fallback_equivalent[input_anchored]("1" + "a" * 255 + "END")
    assert_fallback_equivalent[input_anchored]("prefix " + "a" * 32 + "END")


def test_anchored_fallback_equivalence() raises:
    comptime required_literal_line = Regex("[ -~]*ABCDEFGHIJKLMNOPQRSTUVWXYZ.*")
    assert_fallback_equivalent[required_literal_line](
        "first line\nabcABCDEFGHIJKLMNOPQRSTUVWXYZ!\nlast"
    )
    assert_fallback_equivalent[required_literal_line]("no required literal")

    comptime required_literal_end = Regex("[ -~]*ABCDEFGHIJKLMNOPQRSTUVWXYZ$")
    assert_fallback_equivalent[required_literal_end](
        "first line\nabcABCDEFGHIJKLMNOPQRSTUVWXYZ"
    )
    assert_fallback_equivalent[required_literal_end](
        "abcABCDEFGHIJKLMNOPQRSTUVWXYZ\n"
    )
    assert_fallback_equivalent[required_literal_end]("no required literal")

    comptime fixed_end = Regex("[A-Z]END$")
    assert_fallback_equivalent[fixed_end]("prefix ZEND")
    assert_fallback_equivalent[fixed_end]("prefix ZEND\n")
    assert_fallback_equivalent[fixed_end]("prefix ZEND trailing")

    comptime one_byte_end = Regex("\\s$")
    assert_fallback_equivalent[one_byte_end](" \n")


def test_run_fallback_equivalence() raises:
    comptime bounded_byte_run = Regex("[A-Za-z]{2,3}")
    assert_fallback_equivalent[bounded_byte_run]("a ab abc abcd 12 XY")
    assert_fallback_equivalent[bounded_byte_run]("1" * 256)

    comptime long_byte_run = Regex("[a-z]{65,}")
    assert_fallback_equivalent[long_byte_run]("1" * 128 + "a" * 65)
    assert_fallback_equivalent[long_byte_run]("a" * 64 + "1" * 128)

    comptime fixed_predicates = Regex("\\w{2}\\s\\w{3}\\s\\w{4}")
    assert_fallback_equivalent[fixed_predicates](
        "ab cde fghi! xx yyy zzzz! malformed"
    )

    comptime folded_fixed = Regex("Sherlock Holmes", case_insensitive=True)
    assert_fallback_equivalent[folded_fixed](
        "SHERLOCK HOLMES / sherlock holmes / Sherlock xolmes"
    )


def test_alternation_fallback_equivalence() raises:
    comptime fixed_alternation = Regex("(?:cat|dog)[0-9]{2}")
    assert_fallback_equivalent[fixed_alternation](
        "cat12 dog99 fox12 dog9 cat123"
    )

    comptime fixed_nested_alternation = Regex(
        "(?:ASIA|AKIA|AROA|AIDA)[A-Z0-7]{16}"
    )
    assert_fallback_equivalent[fixed_nested_alternation](
        "x AKIA01234567ABCDEFGH y ASIA0123-invalid"
    )

    comptime literal_alternation = Regex("Sherlock|Holmes|Watson")
    assert_fallback_equivalent[literal_alternation](
        "Watson met Sherlock and Holmes"
    )

    comptime prefixed_alternation = Regex("Tom.{2,5}river|river.{2,5}Tom")
    assert_fallback_equivalent[prefixed_alternation](
        "Tom--river river...Tom Tomriver"
    )

    comptime bounded_prefix_alternation = Regex(".{0,2}(Tom|Sawyer|Finn)")
    assert_fallback_equivalent[bounded_prefix_alternation](
        "xxTom Sawyer yyFinn"
    )

    comptime greedy_complement = Regex(".*[^A-Z]|[A-Z]")
    assert_fallback_equivalent[greedy_complement]("lower Z tail\nABC")


def assert_ast_nfa_equivalent[
    regex: Regex
](text: StringSpan, start: Int) raises:
    var actual = _match_node[regex.nodes, regex.root](text, start)
    var expected = _nfa_match_at[regex](text, start)
    assert_equal(Bool(actual), Bool(expected))
    if actual and expected:
        assert_equal(
            actual.unsafe_value().consumed(),
            expected.unsafe_value().consumed(),
        )


def test_generic_byte_run_boundaries() raises:
    # Compare against the independent ordered NFA at every SIMD lane and
    # several unaligned starts, both at a rejecting byte and at the span end.
    comptime greedy = Regex("[a-z]+")
    comptime bounded = Regex("[a-z]{2,67}")
    comptime lazy = Regex("[a-z]{2,67}?")
    comptime long_lazy = Regex("[a-z]{65,67}?")
    comptime giveback = Regex("[a-z]{2,67}a!")
    comptime negated = Regex("[^!]*!")
    comptime dot = Regex(".*!")
    for start in range(4):
        for length in range(2 * CLASS_SIMD_WIDTH + 5):
            var text = "#" * start + "a" * length + "!tail"
            var span = text[byte = 0 : text.byte_length()]
            assert_ast_nfa_equivalent[greedy](span, start)
            assert_ast_nfa_equivalent[bounded](span, start)
            assert_ast_nfa_equivalent[lazy](span, start)
            assert_ast_nfa_equivalent[long_lazy](span, start)
            assert_ast_nfa_equivalent[giveback](span, start)
            assert_ast_nfa_equivalent[negated](span, start)
            assert_ast_nfa_equivalent[dot](span, start)
            var truncated = span[byte = 0 : start + length]
            assert_ast_nfa_equivalent[greedy](truncated, start)
            assert_ast_nfa_equivalent[bounded](truncated, start)
            assert_ast_nfa_equivalent[negated](truncated, start)


def test_generic_byte_run_semantics() raises:
    comptime byte_dot = Regex(".+!")
    comptime unicode_dot = Regex(".+!", unicode=True)
    comptime dotall = Regex("(?s).+!")
    comptime lazy_suffix = Regex("[a-z]+?a!")
    comptime empty = Regex("[a-z]*")
    var cases: List[String] = ["", "!", "aaa!", "a" * 130 + "!", "a\na!", "é💩!"]
    for text in cases:
        var span = text[byte = 0 : text.byte_length()]
        assert_ast_nfa_equivalent[byte_dot](span, 0)
        # Variable-width Unicode repeats use the NFA through public dispatch.
        assert_equal(
            matches[unicode_dot](text), _nfa_full_match[unicode_dot](span)
        )
        assert_ast_nfa_equivalent[dotall](span, 0)
        assert_ast_nfa_equivalent[lazy_suffix](span, 0)
        assert_ast_nfa_equivalent[empty](span, 0)


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
