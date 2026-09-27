"""Focused tests for shared AST analysis primitives."""

from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import Regex
from moregex._ast_equal import _same_ast_node, _same_bracket_class
from moregex._width import (
    _semantic_fixed_width,
    _semantic_maximum_width,
    _semantic_minimum_width,
)


def test_shared_width_analysis() raises:
    var fixed = Regex("(?:ab|cd){2}")
    assert_equal(_semantic_minimum_width(fixed.nodes, fixed.root), 4)
    assert_equal(_semantic_fixed_width(fixed.nodes, fixed.root), 4)
    assert_equal(_semantic_maximum_width(fixed.nodes, fixed.root), 4)

    var variable = Regex("a(?:bc)?d+")
    assert_equal(_semantic_minimum_width(variable.nodes, variable.root), 2)
    assert_equal(_semantic_fixed_width(variable.nodes, variable.root), -1)
    assert_equal(_semantic_maximum_width(variable.nodes, variable.root), -1)

    var unicode_dot = Regex(".", unicode=True)
    assert_equal(
        _semantic_minimum_width(unicode_dot.nodes, unicode_dot.root), 1
    )
    assert_equal(_semantic_fixed_width(unicode_dot.nodes, unicode_dot.root), -1)
    assert_equal(
        _semantic_maximum_width(unicode_dot.nodes, unicode_dot.root), 4
    )


def test_structural_ast_equality() raises:
    var left = Regex("(ab|cd)+")
    var same = Regex("(ab|cd)+")
    var different = Regex("(ab|ce)+")
    assert_true(
        _same_ast_node(
            left.nodes,
            left.capture_root,
            same.nodes,
            same.capture_root,
        )
    )
    assert_false(
        _same_ast_node(
            left.nodes,
            left.capture_root,
            different.nodes,
            different.capture_root,
        )
    )


def test_bracket_ranges_are_canonical() raises:
    var bridged = Regex("[a-bd-ec]")
    var canonical = Regex("[a-e]")
    assert_true(
        _same_ast_node(
            bridged.nodes,
            bridged.root,
            canonical.nodes,
            canonical.root,
        )
    )


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
