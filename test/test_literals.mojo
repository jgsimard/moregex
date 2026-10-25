from std.testing import TestSuite, assert_false, assert_true
from moregex._runtime import matches_runtime

from moregex import Regex, matches


def test_literals() raises:
    comptime empty = Regex("")
    assert_true(matches[empty](""))
    assert_false(matches[empty]("x"))

    comptime literal = Regex("hello")
    assert_true(matches[literal]("hello"))
    assert_false(matches[literal]("hell"))
    assert_false(matches[literal]("hello!"))
    assert_false(matches[literal]("Hello"))


def test_escaped_literals() raises:
    comptime escaped = Regex("a\\.b\\*c\\?d\\|e\\(f\\)g\\\\")
    assert_true(matches[escaped]("a.b*c?d|e(f)g\\"))
    assert_false(matches[escaped]("aXb*c?d|e(f)g\\"))


def test_runtime_literals() raises:
    # The reference runtime interpreter must agree.
    var runtime_literal = Regex("hello")
    assert_true(matches_runtime(runtime_literal, "hello"))
    assert_false(matches_runtime(runtime_literal, "hell"))
    var runtime_pattern = String("world")
    var runtime_owned = Regex(runtime_pattern)
    assert_true(matches_runtime(runtime_owned, "world"))

    var anchored = Regex("^az$")
    assert_true(matches_runtime(anchored, "az"))
    assert_false(matches_runtime(anchored, "xaz"))
    var bounded = Regex("\\baz\\b")
    assert_true(matches_runtime(bounded, "az"))
    assert_false(matches_runtime(bounded, "_az"))


def run_tests[_discovery: Bool = True]() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
