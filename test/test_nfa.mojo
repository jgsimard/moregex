"""Correctness checks for generic Thompson-NFA execution."""

from std.testing import TestSuite, assert_equal, assert_true

from moregex import Regex, search
from moregex._nfa import (
    _nfa_find_capture_participation,
    _nfa_find_captures,
    _nfa_find_from,
    _nfa_full_match,
    _nfa_match_captures_at,
    _nfa_search,
)


def assert_nfa_search[regex: Regex](text: String, expected: Bool) raises:
    var span = text[byte = 0 : text.byte_length()]
    assert_equal(_nfa_search[regex](span), expected)


def assert_public_search[regex: Regex](text: String, expected: Bool) raises:
    assert_equal(search[regex](text), expected)


def assert_nfa_full[regex: Regex](text: String, expected: Bool) raises:
    var span = text[byte = 0 : text.byte_length()]
    assert_equal(_nfa_full_match[regex](span), expected)


def assert_nfa_find[
    regex: Regex
](text: String, start: Int, consumed: Int) raises:
    var span = text[byte = 0 : text.byte_length()]
    var result = _nfa_find_from[regex](span, 0)
    assert_true(result)
    assert_equal(result.unsafe_value().start, start)
    assert_equal(result.unsafe_value().consumed(), consumed)


def test_basic_nfa_search() raises:
    comptime literal = Regex("cat")
    assert_nfa_search[literal]("a cat naps", True)
    assert_nfa_search[literal]("dogs", False)

    comptime alternation = Regex("cat|dog")
    assert_nfa_search[alternation]("a dog runs", True)
    assert_nfa_search[alternation]("fox", False)

    comptime repeated_alternation = Regex("(?:ab|cd)+!")
    assert_nfa_search[repeated_alternation]("xxabcdab!yy", True)
    assert_nfa_search[repeated_alternation]("xxabcdab?yy", False)

    comptime classes = Regex("[a-z]+:[0-9]+")
    assert_nfa_search[classes]("__abc:123__", True)
    assert_nfa_search[classes]("__abc:xyz__", False)

    comptime negated = Regex("[^0-9]+!")
    assert_nfa_search[negated]("123abc!456", True)
    assert_nfa_search[negated]("123456", False)


def test_nfa_flags_and_boundaries() raises:
    comptime multiline = Regex("(?m)^cat$")
    assert_nfa_search[multiline]("dog\ncat\nfox", True)
    assert_nfa_search[multiline]("dog\nscatter\nfox", False)

    comptime boundary = Regex("\\bcat\\b")
    assert_nfa_search[boundary]("a cat!", True)
    assert_nfa_search[boundary]("scatter", False)

    comptime lazy_suffix = Regex("a+?b")
    assert_nfa_search[lazy_suffix]("xxaaabyy", True)
    assert_nfa_search[lazy_suffix]("xxaaayyb", False)

    comptime bounded = Regex("a{2,4}b")
    assert_nfa_search[bounded]("xaaabx", True)
    assert_nfa_search[bounded]("xax", False)

    comptime folded = Regex("(?i)[a-f]+:cat")
    assert_nfa_search[folded]("__AbCd:CAT__", True)
    assert_nfa_search[folded]("__xyz:cat__", False)


def test_ordered_nfa_execution() raises:
    # The ordered executor must reconsider an earlier alternative when its
    # continuation fails, while retaining branch and quantifier priority.
    comptime reconsider = Regex("(a|aa)c")
    assert_nfa_full[reconsider]("aac", True)
    assert_public_search[reconsider]("zzaac", True)
    assert_nfa_find[reconsider]("ac", 0, 2)
    assert_nfa_full[reconsider]("ac", True)
    assert_nfa_find[reconsider]("zzaac!", 2, 3)
    comptime root_reconsider = Regex("(a|ab)+")
    assert_nfa_full[root_reconsider]("ab", True)
    comptime empty_first = Regex("(|x)")
    assert_nfa_full[empty_first]("", True)
    assert_nfa_full[empty_first]("x", True)

    comptime nested_giveback = Regex("(a+)*ab")
    assert_nfa_full[nested_giveback]("aaab", True)
    assert_nfa_full[nested_giveback]("aaa", False)
    comptime greedy = Regex("a*")
    assert_nfa_find[greedy]("aaab", 0, 3)
    comptime lazy = Regex("a+?")
    assert_nfa_find[lazy]("aaab", 0, 1)
    comptime ordered_short = Regex("a|aa")
    assert_nfa_find[ordered_short]("aa", 0, 1)
    comptime ordered_long = Regex("aa|a")
    assert_nfa_find[ordered_long]("aa", 0, 2)

    # Boolean full matching can discard priority while retaining assertion and
    # end-of-input semantics.
    comptime shared_prefix = Regex("^(?:apple|application|apply):[0-9]+$")
    assert_nfa_full[shared_prefix]("application:12345", True)
    assert_nfa_full[shared_prefix]("applenotvalid:12345", False)
    assert_nfa_full[shared_prefix]("apple:12345\n", False)


def test_ordered_nfa_payload_equivalence() raises:
    """All ordered executor payloads must select the same prioritized match."""
    comptime captured = Regex("(aa|a)(b)?")
    var text = "zzaab!"
    var span = text[byte = 0 : text.byte_length()]

    var plain = _nfa_find_from[captured](span, 0).unsafe_value()
    var offsets = _nfa_find_captures[captured](span, 0).unsafe_value()
    var participation = _nfa_find_capture_participation[captured](
        span, 0
    ).unsafe_value()
    var anchored = _nfa_match_captures_at[captured](span, 2).unsafe_value()

    assert_equal(plain.start, 2)
    assert_equal(plain.end, 5)
    assert_equal(offsets.starts[0], plain.start)
    assert_equal(offsets.ends[0], plain.end)
    assert_equal(offsets.starts[1], 2)
    assert_equal(offsets.ends[1], 4)
    assert_equal(offsets.starts[2], 4)
    assert_equal(offsets.ends[2], 5)
    assert_equal(participation.span.start, plain.start)
    assert_equal(participation.span.end, plain.end)
    assert_equal(participation.groups, UInt64(3))
    assert_equal(anchored.starts[0], plain.start)
    assert_equal(anchored.ends[0], plain.end)

    comptime optional = Regex("(aa|a)(b)?")
    var missing_text = "zzaa!"
    var missing_span = missing_text[byte = 0 : missing_text.byte_length()]
    var missing = _nfa_find_captures[optional](missing_span, 0).unsafe_value()
    var missing_participation = _nfa_find_capture_participation[optional](
        missing_span, 0
    ).unsafe_value()
    assert_equal(missing.starts[2], -1)
    assert_equal(missing.ends[2], -1)
    assert_equal(missing_participation.groups, UInt64(1))

    comptime lazy = Regex("(a+?)(a)")
    var lazy_text = "aaa"
    var lazy_span = lazy_text[byte = 0 : lazy_text.byte_length()]
    var lazy_plain = _nfa_find_from[lazy](lazy_span, 0).unsafe_value()
    var lazy_offsets = _nfa_find_captures[lazy](lazy_span, 0).unsafe_value()
    assert_equal(lazy_plain.end, 2)
    assert_equal(lazy_offsets.starts[1], 0)
    assert_equal(lazy_offsets.ends[1], 1)
    assert_equal(lazy_offsets.starts[2], 1)
    assert_equal(lazy_offsets.ends[2], 2)


def test_large_ordered_full_match() raises:
    # This exceeds the 64-state Boolean executor and needs strict-end path
    # exploration, including reconsidering the shorter first alternative.
    comptime repeated = Regex("(a|ab){40}")
    var text = "ab" * 40
    assert_nfa_full[repeated](text, True)
    assert_nfa_full[repeated](text + "x", False)
    assert_nfa_full[repeated](text + "\n", False)
    assert_nfa_full[repeated]("ab" * 39, False)


def test_unicode_nfa_execution() raises:
    # Unicode dot lowers to disjoint 1-4-byte Thompson branches and therefore
    # participates in the same ordered continuation semantics.
    comptime unicode_suffix = Regex(".+x", unicode=True)
    assert_nfa_full[unicode_suffix]("💩x", True)
    assert_nfa_find[unicode_suffix]("zz💩x", 0, 7)
    comptime nested_unicode = Regex("(.+)*x", unicode=True)
    assert_nfa_full[nested_unicode]("💩x", True)


def test_public_hybrid_nfa_search() raises:
    # These shapes select the hybrid NFA path in the public generic search.
    comptime broad_suffix = Regex(".+[A-Z]")
    assert_public_search[broad_suffix]("a" * 256, False)
    assert_public_search[broad_suffix]("a" * 255 + "Z", True)
    comptime repeated_suffix = Regex("(?:ab|cd)+!")
    assert_public_search[repeated_suffix]("ab" * 128, False)
    assert_public_search[repeated_suffix]("xx" + "ab" * 8 + "!", True)

    # Semantic-risk searches with an exact leading literal should preserve
    # ordered behavior while skipping directly to possible match starts.
    comptime lazy_delimited = Regex("<<tag.*?>>")
    assert_public_search[lazy_delimited]("x" * 256, False)
    assert_public_search[lazy_delimited]("x" * 256 + "<<tag value>>", True)
    assert_public_search[lazy_delimited]("<<tag\nvalue>>", False)
    assert_public_search[lazy_delimited](
        "<<tag\n" + "x" * 256 + "<<tag value>>", True
    )
    assert_public_search[lazy_delimited]("<<tag bad\n<<tag good>>", True)

    # A dense leading prefix must retain the linear fallback after one probe.
    comptime dense_prefix = Regex("a.*?b")
    assert_public_search[dense_prefix]("a" * 1024, False)
    assert_public_search[dense_prefix]("a" * 1024 + "b", True)

    comptime dotall_delimited = Regex("(?s)<block>.*?</block>")
    assert_public_search[dotall_delimited]("x" * 256, False)
    assert_public_search[dotall_delimited](
        "x" * 256 + "<block>line 1\nline 2</block>", True
    )
    assert_public_search[dotall_delimited]("<block>unterminated", False)


def test_large_literal_alternation_search() raises:
    comptime alternatives = Regex("foo|bar|baz|qux|quux|corge|grault|garply")
    assert_public_search[alternatives]("x" * 1024, False)
    assert_public_search[alternatives]("x" * 1024 + "garply", True)
    assert_public_search[alternatives]("x" * 63 + "grault", True)


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
