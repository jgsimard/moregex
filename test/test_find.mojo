"""Match spans, numbered captures, and non-overlapping iteration."""

from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import Regex, find, find_span, finditer, finditer_span


def test_template_captures() raises:
    comptime template = Regex("\\{\\{(.*?)\\}\\}")
    var text = "<h1>{{TITLE}}</h1><p>{{ FIRST_NAME0 }}</p>"
    var found = finditer[template](text)
    assert_equal(len(found), 2)

    assert_equal(found[0].start(), 4)
    assert_equal(found[0].end(), 13)
    assert_equal(found[0].span(), (4, 13))
    assert_equal(found[0].start(1), 6)
    assert_equal(found[0].end(1), 11)
    assert_equal(found[0].group(text), "{{TITLE}}")
    assert_equal(found[0].group(text, 1), "TITLE")

    assert_equal(found[1].start(), 21)
    assert_equal(found[1].end(), 38)
    assert_equal(found[1].group(text, 1), " FIRST_NAME0 ")


def test_nested_optional_and_alternated_captures() raises:
    comptime nested = Regex("(a(b)?)(c)")
    var text = "xxabc ac"
    var found = finditer[nested](text)
    assert_equal(len(found), 2)
    assert_equal(found[0].group_count(), 3)
    assert_equal(found[0].group(text, 1), "ab")
    assert_equal(found[0].group(text, 2), "b")
    assert_equal(found[0].group(text, 3), "c")
    assert_equal(found[1].group(text, 1), "a")
    assert_equal(found[1].start(2), -1)
    assert_equal(found[1].end(2), -1)
    assert_false(found[1].group_optional(text, 2))
    assert_equal(found[1].group(text, 3), "c")

    comptime alternated = Regex("(a)|(bc)")
    var alternative_text = "xbc"
    var alternative = find[alternated](alternative_text)
    assert_true(alternative)
    var selected = alternative.unsafe_value()
    assert_equal(selected.start(1), -1)
    assert_equal(selected.group(alternative_text, 2), "bc")

    comptime greedy = Regex("(a+)(a)")
    var greedy_text = "aaa"
    var greedy_match = find[greedy](greedy_text).unsafe_value()
    assert_equal(greedy_match.group(greedy_text, 1), "aa")
    assert_equal(greedy_match.group(greedy_text, 2), "a")

    comptime lazy = Regex("(a+?)(a)")
    var lazy_match = find[lazy](greedy_text).unsafe_value()
    assert_equal(lazy_match.span(), (0, 2))
    assert_equal(lazy_match.group(greedy_text, 1), "a")


def test_repeated_empty_and_noncapturing_groups() raises:
    comptime repeated = Regex("(ab)+")
    var repeated_text = "xabab"
    var repetition = find[repeated](repeated_text).unsafe_value()
    assert_equal(repetition.span(), (1, 5))
    assert_equal(repetition.span(1), (3, 5))
    assert_equal(repetition.group(repeated_text, 1), "ab")

    comptime repeated_optional = Regex("((a)|(b))+")
    var optional_text = "ab"
    var optional = find[repeated_optional](optional_text).unsafe_value()
    assert_equal(optional.group(optional_text, 1), "b")
    assert_equal(optional.group(optional_text, 2), "a")
    assert_equal(optional.group(optional_text, 3), "b")

    comptime empty = Regex("(a*)")
    var empty_text = "b"
    var empty_matches = finditer[empty](empty_text)
    assert_equal(len(empty_matches), 2)
    assert_equal(empty_matches[0].span(), (0, 0))
    assert_equal(empty_matches[0].span(1), (0, 0))
    assert_equal(empty_matches[1].span(), (1, 1))

    comptime noncapturing = Regex("(?:x)(y)")
    var noncapturing_text = "xy"
    var grouped = find[noncapturing](noncapturing_text).unsafe_value()
    assert_equal(grouped.group_count(), 1)
    assert_equal(grouped.group(noncapturing_text, 1), "y")


def test_offsets_and_borrowed_input() raises:
    comptime cats = Regex("(cat)")
    var text = "cat cat"
    var second = find[cats](text, 1).unsafe_value()
    assert_equal(second.span(), (4, 7))
    assert_equal(second.group(text, 1), "cat")

    var span = text[byte = 0 : text.byte_length()]
    var borrowed = find_span[cats](span, 1).unsafe_value()
    assert_equal(borrowed.span(1), (4, 7))
    assert_equal(len(finditer_span[cats](span)), 2)

    comptime unicode = Regex("(💩)")
    var unicode_text = "x💩y"
    var unicode_match = find[unicode](unicode_text).unsafe_value()
    assert_equal(unicode_match.span(), (1, 5))
    assert_equal(unicode_match.group(unicode_text, 1), "💩")

    comptime folded = Regex("(?i)(cat)")
    var folded_text = "xxCAT"
    var folded_match = find[folded](folded_text).unsafe_value()
    assert_equal(folded_match.span(), (2, 5))
    assert_equal(folded_match.group(folded_text, 1), "CAT")

    comptime line = Regex("(?m)^(cat)$")
    var lines = "dog\ncat\nfox"
    var line_match = find[line](lines).unsafe_value()
    assert_equal(line_match.span(), (4, 7))
    assert_equal(line_match.span(1), (4, 7))

    comptime line_without_capture = Regex("(?m)^cat$")
    var plain_line_match = find[line_without_capture](lines)
    assert_true(plain_line_match)
    assert_equal(plain_line_match.unsafe_value().span(), (4, 7))

    assert_false(find[cats](text, text.byte_length() + 1))


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
