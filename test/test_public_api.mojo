"""Public naming, owned/span symmetry, and compatibility aliases."""

from std.testing import TestSuite, assert_equal, assert_true

from moregex import (
    Regex,
    count_captures,
    count_line_captures,
    count_matching_lines,
    find,
    findall,
    findall_span,
    finditer,
    grep,
    grep_captures,
    matched_bytes,
    matched_bytes_span,
    matches_span,
)


def test_owned_and_borrowed_entry_points() raises:
    comptime repeated = Regex("ab+")
    var text = "abb x ab"
    var span = text[byte = 0 : text.byte_length()]
    assert_true(matches_span[repeated]("abbb"[byte=0:4]))
    assert_equal(matched_bytes[repeated](text), 5)
    assert_equal(matched_bytes_span[repeated](span), 5)
    assert_equal(len(findall[repeated](text)), 2)
    assert_equal(len(findall_span[repeated](span)), 2)
    assert_equal(len(finditer[repeated](text)), 2)


def test_borrowed_capture_extraction() raises:
    comptime captured = Regex("(ab)")
    var text = "xxabyy"
    var span = text[byte = 0 : text.byte_length()]
    var found = find[captured](text).unsafe_value()
    assert_equal(String(found.group_span(span, 1)), "ab")


def test_line_and_capture_names() raises:
    comptime captured = Regex("(a)(b)?")
    assert_equal(count_captures[captured]("ab a"), 5)

    comptime cat = Regex("cat")
    var lines = "cat\nx\nbobcat\n"
    assert_equal(count_matching_lines[cat](lines), 2)
    assert_equal(grep[cat](lines), 2)

    comptime one_capture = Regex("(a)")
    var capture_lines = "a\nx\naa\n"
    assert_equal(count_line_captures[one_capture](capture_lines), 6)
    assert_equal(grep_captures[one_capture](capture_lines), 6)


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
