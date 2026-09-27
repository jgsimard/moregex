"""Focused tests for shared executor result representations."""

from std.testing import TestSuite, assert_equal, assert_false, assert_true
from std.utils import StaticTuple

from moregex._result import (
    _CaptureOffsets,
    _CaptureParticipation,
    _MatchSpan,
)


def test_match_span() raises:
    var span = _MatchSpan(3, 9)
    assert_equal(span.consumed(), 6)
    assert_false(span.is_empty())
    assert_true(_MatchSpan(4, 4).is_empty())


def test_capture_payloads() raises:
    var starts = StaticTuple[Int, 3](3, 4, -1)
    var ends = StaticTuple[Int, 3](9, 7, -1)
    var captures = _CaptureOffsets[2](starts, ends)
    assert_equal(captures.match_span().start, 3)
    assert_equal(captures.match_span().end, 9)
    var participation = _CaptureParticipation(captures.match_span(), 1)
    assert_equal(participation.span.consumed(), 6)
    assert_equal(participation.groups, 1)


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
