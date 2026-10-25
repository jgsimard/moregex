"""Literal-delimited templates and equivalence with the ordered NFA."""

from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import (
    Regex,
    count,
    count_captures,
    count_spans,
    find,
    find_span,
    finditer,
    matches,
    search,
)
from moregex._delimited import _literal_delimited_plan
from moregex._nfa import _nfa_find_captures, _nfa_find_from, _nfa_full_match


def assert_delimited_equivalent[regex: Regex](text: String) raises:
    """Compare public dispatch, captures, and iteration to the original NFA."""
    var span = text[byte = 0 : text.byte_length()]
    assert_equal(matches[regex](text), _nfa_full_match[regex](span))
    var start = 0
    var total = 0
    var matched_bytes = 0
    while start <= text.byte_length():
        var expected = _nfa_find_from[regex](span, start)
        var actual = find_span[regex](span, start)
        assert_equal(Bool(actual), Bool(expected))
        if not expected:
            break
        var expected_span = expected.unsafe_value()
        var found = actual.unsafe_value()
        assert_equal(found.start(), expected_span.start)
        assert_equal(found.end(), expected_span.end)
        comptime if regex.capture_count > 0:
            var captured = _nfa_find_captures[regex](span, start)
            assert_true(captured)
            var offsets = captured.unsafe_value()
            comptime for group in range(1, regex.capture_count + 1):
                assert_equal(found.start(group), offsets.starts[group])
                assert_equal(found.end(group), offsets.ends[group])
        total += 1
        matched_bytes += expected_span.consumed()
        start = expected_span.end
    assert_equal(search[regex](text), total > 0)
    assert_equal(count[regex](text), total)
    assert_equal(count_spans[regex](text), matched_bytes)
    assert_equal(count_captures[regex](text), total * (regex.capture_count + 1))
    assert_equal(len(finditer[regex](text)), total)


def test_template_delimiter_plan() raises:
    comptime template = Regex(r"\{\{(.*?)\}\}")
    comptime plan = _literal_delimited_plan[template]()
    assert_true(plan)
    assert_equal(plan.unsafe_value().prefix, "{{")
    assert_equal(plan.unsafe_value().suffix, "}}")
    assert_false(plan.unsafe_value().dotall)

    comptime dollar = Regex(r"\$\{(.*?)\}")
    comptime percent = Regex("<%(.*?)%>")
    comptime plain = Regex(r"\{\{.*?\}\}")
    comptime dotall = Regex(r"(?s)\{\{(.*?)\}\}")
    assert_true(_literal_delimited_plan[dollar]())
    assert_true(_literal_delimited_plan[percent]())
    assert_true(_literal_delimited_plan[plain]())
    assert_true(_literal_delimited_plan[dotall]().unsafe_value().dotall)

    comptime greedy = Regex(r"\{\{(.*)\}\}")
    comptime bounded = Regex(r"\{\{(.{0,8}?)\}\}")
    comptime word = Regex(r"\{\{(\w*?)\}\}")
    comptime nested = Regex(r"\{\{((.*?))\}\}")
    comptime anchored = Regex(r"^\{\{(.*?)\}\}$")
    comptime unicode = Regex(r"\{\{(.*?)\}\}", unicode=True)
    comptime folded = Regex("(?i)begin(.*?)end")
    comptime missing_prefix = Regex("(.*?)end")
    comptime missing_suffix = Regex("begin(.*?)")
    assert_false(_literal_delimited_plan[greedy]())
    assert_false(_literal_delimited_plan[bounded]())
    assert_false(_literal_delimited_plan[word]())
    assert_false(_literal_delimited_plan[nested]())
    assert_false(_literal_delimited_plan[anchored]())
    assert_false(_literal_delimited_plan[unicode]())
    assert_false(_literal_delimited_plan[folded]())
    assert_false(_literal_delimited_plan[missing_prefix]())
    assert_false(_literal_delimited_plan[missing_suffix]())


def test_template_empty_adjacent_and_nested_placeholders() raises:
    comptime template = Regex(r"\{\{(.*?)\}\}")
    var text = "{{}}{{a}}{{b}} tail {{outer {{inner}} {{unfinished"
    var found = finditer[template](text)
    assert_equal(len(found), 4)
    assert_equal(found[0].span(), (0, 4))
    assert_equal(found[0].span(1), (2, 2))
    assert_equal(found[0].group(text, 1), "")
    assert_equal(found[1].group(text, 1), "a")
    assert_equal(found[2].group(text, 1), "b")
    assert_equal(found[3].group(text, 1), "outer {{inner")
    assert_delimited_equivalent[template](text)
    assert_delimited_equivalent[template]("{{NAME}} and {{OTHER}}")
    assert_delimited_equivalent[template]("x{{💥}}y")
    assert_delimited_equivalent[template]("{{missing")
    assert_delimited_equivalent[template]("}} before {{")
    assert_delimited_equivalent[template]("")

    # Full matching must extend past earlier closers when necessary.
    assert_true(matches[template]("{{first}}{{second}}"))
    assert_false(matches[template]("prefix {{first}}"))


def test_template_newlines_and_literal_newline_delimiters() raises:
    comptime template = Regex(r"\{\{(.*?)\}\}")
    comptime dotall = Regex(r"(?s)\{\{(.*?)\}\}")
    var text = "{{bad\n{{good}}\r\n{{also\rbad}}"
    var found = finditer[template](text)
    assert_equal(len(found), 2)
    assert_equal(found[0].group(text, 1), "good")
    assert_equal(found[1].group(text, 1), "also\rbad")
    assert_delimited_equivalent[template](text)
    assert_delimited_equivalent[dotall](text)
    assert_equal(
        find[dotall](text).unsafe_value().group(text, 1), "bad\n{{good"
    )

    # A later opener can straddle the LF that invalidated an earlier opener.
    comptime newline_prefix = Regex("a\n(.*?)z")
    var newline_text = "a\nx a\nz"
    assert_equal(
        find[newline_prefix](newline_text).unsafe_value().span(), (4, 7)
    )
    assert_delimited_equivalent[newline_prefix](newline_text)
    comptime newline_suffix = Regex("a(.*?)\nz")
    assert_delimited_equivalent[newline_suffix]("aa\nz a\nx a\nz")


def test_template_start_offsets_and_overlapping_delimiters() raises:
    comptime template = Regex(r"\{\{(.*?)\}\}")
    var text = "{{a}}{{b}}"
    var span = text[byte = 0 : text.byte_length()]
    for start in range(-1, text.byte_length() + 2):
        var actual = find_span[template](span, start)
        var expected = _nfa_find_captures[template](span, max(0, start))
        assert_equal(Bool(actual), Bool(expected))
        if expected:
            var offsets = expected.unsafe_value()
            var found = actual.unsafe_value()
            assert_equal(found.span(), (offsets.starts[0], offsets.ends[0]))
            assert_equal(found.span(1), (offsets.starts[1], offsets.ends[1]))

    comptime same_delimiter = Regex("aa(.*?)aa")
    assert_delimited_equivalent[same_delimiter]("aaaaaaa aaaa aa\naaaa")
    assert_delimited_equivalent[template]("{{{}}} {{{{}}}} {{\n{{}}")
    comptime dollar = Regex(r"\$\{(.*?)\}")
    assert_delimited_equivalent[dollar]("${NAME} ${} ${nested ${name}}")
    comptime percent = Regex("<%(.*?)%>")
    assert_delimited_equivalent[percent]("<% a %><%%> <%\n<% b %>")


def test_template_exhaustive_nfa_equivalence() raises:
    comptime template = Regex(r"\{\{(.*?)\}\}")
    comptime dotall = Regex(r"(?s)\{\{(.*?)\}\}")
    comptime plain = Regex(r"\{\{.*?\}\}")
    # All strings of up to six bytes, covering partial/overlapping delimiters,
    # empty bodies, ordinary content, and LF boundaries (5,461 inputs).
    var alphabet: List[String] = ["{", "}", "a", "\n"]
    var combinations = 1
    for length in range(7):
        for code in range(combinations):
            var value = code
            var text = String()
            for _ in range(length):
                text += alphabet[value % 4]
                value //= 4
            assert_delimited_equivalent[template](text)
            assert_delimited_equivalent[dotall](text)
            assert_delimited_equivalent[plain](text)
        combinations *= 4


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
