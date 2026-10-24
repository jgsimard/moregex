from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import Regex, count, count_spans, matches, search, search_span


def test_email_patterns() raises:
    comptime email = Regex(
        "\\w+(\\+\\w*)?@(\\d+\\.\\d+\\.\\d+\\.\\d+|\\w+\\.\\w+)"
    )
    assert_true(matches[email]("user@example.com"))
    assert_false(matches[email]("uexample.com"))
    assert_false(matches[email]("user@ecom"))
    assert_true(matches[email]("user+tag@example.com"))
    assert_false(matches[email]("user@100"))
    assert_true(matches[email]("howdy123@1.2.3.4"))
    assert_false(matches[email]("howdy1231.2.3.4"))
    assert_false(matches[email]("howdy123@1/2/3/4"))


def test_email_infix_search() raises:
    # This is Rebar's email pattern and exercises its single-pass infix search.
    comptime rebar_email = Regex("([^ @]+)@([^ @]+)")
    assert_true(search[rebar_email]("before alice@example.com after"))
    assert_false(search[rebar_email]("alice @example.com"))
    assert_false(search[rebar_email]("alice@ example.com"))
    assert_false(search[rebar_email]("alice@@example.com"))
    assert_false(search[rebar_email]("@example.com alice@"))
    assert_true(search[rebar_email]("bad@ @bad then bob@example.com"))
    assert_true(search[rebar_email]("x" * 63 + "a@b"))
    assert_true(search[rebar_email]("x" * 62 + "a@b"))
    assert_true(search[rebar_email]("x" * 30 + "a@b"))
    assert_true(search[rebar_email]("x" * 14 + "a@b"))
    assert_true(search[rebar_email]("x" * 6 + "a@b"))
    assert_true(search[rebar_email]("x" * 2 + "a@b"))


def test_bracket_email_counting_and_borrowed_search() raises:
    comptime bracket_email = Regex("[\\w\\.+-]+@[\\w\\.-]+\\.[\\w\\.-]+")
    var bracket_email_text = (
        "alice@example.com invalid@host bob+tag@sub.example.org"
    )
    assert_equal(count[bracket_email](bracket_email_text), 2)
    assert_equal(count_spans[bracket_email](bracket_email_text), 40)

    comptime rebar_email = Regex("([^ @]+)@([^ @]+)")
    var borrowed_text = String("prefix alice@example.com suffix")
    var borrowed = borrowed_text[byte=7:24]
    assert_true(search_span[rebar_email](borrowed))

    comptime literal = Regex("example")
    assert_true(search_span[literal](borrowed))


def test_mandatory_infix_search() raises:
    # The infix optimization is structural rather than email-specific.
    comptime key_value = Regex("[^:]+:[0-9]+")
    assert_true(search[key_value]("prefix key:42 suffix"))
    assert_false(search[key_value]("prefix key:value suffix"))

    comptime uri = Regex("([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?")
    assert_true(search[uri]("see http://example.com/path now"))
    assert_false(search[uri]("123://example.com"))
    assert_false(search[uri]("http:///path"))
    assert_false(search[uri]("http:// example.com"))
    assert_true(search[uri]("x" * 60 + "http://a"))
    assert_true(search[uri]("x" * 59 + "http://a"))
    assert_true(search[uri]("x" * 27 + "http://a"))
    assert_true(search[uri]("x" * 11 + "http://a"))
    assert_true(search[uri]("x" * 3 + "http://a"))
    assert_true(search[uri]("abc://a"))


def test_imported_uri_and_mapping_patterns() raises:
    comptime imported_uri = Regex(
        "[\\w]+://[^/\\s?#]+[^\\s?#]+(?:\\?[^\\s#]*)?(?:#[^\\s]*)?"
    )
    var imported_uri_text = (
        "see http://example.com/path?x=1#frag then ftp://host/a x://a"
    )
    assert_equal(count[imported_uri](imported_uri_text), 2)
    assert_equal(count_spans[imported_uri](imported_uri_text), 44)

    # The mandatory-infix optimization is not tied to URI punctuation.
    comptime mapping = Regex("[A-Z][A-Z0-9]*=>[a-z]+")
    assert_true(search[mapping]("prefix A19=>value suffix"))
    assert_false(search[mapping]("prefix 19=>value suffix"))


def test_uri_or_email_alternation() raises:
    comptime uri_or_email = Regex(
        "([a-zA-Z][a-zA-Z0-9]*)://([^ /]+)(/[^ ]*)?|([^ @]+)@([^ @]+)"
    )
    assert_true(search[uri_or_email]("contact alice@example.com"))
    assert_true(search[uri_or_email]("visit https://example.com/path"))
    assert_false(search[uri_or_email]("there is no address here"))


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
