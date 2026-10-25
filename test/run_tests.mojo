"""Run the moregex runtime tests in one process."""

from test.runner import TestRunner, module_selected

import test.test_ast_foundations as test_ast_foundations
import test.test_capabilities as test_capabilities
import test.test_delimited as test_delimited
import test.test_email as test_email
import test.test_fallback as test_fallback
import test.test_find as test_find
import test.test_literals as test_literals
import test.test_nfa as test_nfa
import test.test_public_api as test_public_api
import test.test_result_foundations as test_result_foundations
import test.test_simd_equivalence as test_simd_equivalence
import test.test_syntax as test_syntax


def main() raises:
    var tests = TestRunner()
    comptime if module_selected["test_ast_foundations"]():
        tests.run(
            "test/test_ast_foundations.mojo",
            test_ast_foundations.run_tests[True],
        )
    comptime if module_selected["test_capabilities"]():
        tests.run(
            "test/test_capabilities.mojo", test_capabilities.run_tests[True]
        )
    comptime if module_selected["test_email"]():
        tests.run("test/test_email.mojo", test_email.run_tests[True])
    comptime if module_selected["test_delimited"]():
        tests.run("test/test_delimited.mojo", test_delimited.run_tests[True])
    comptime if module_selected["test_fallback"]():
        tests.run("test/test_fallback.mojo", test_fallback.run_tests[True])
    comptime if module_selected["test_find"]():
        tests.run("test/test_find.mojo", test_find.run_tests[True])
    comptime if module_selected["test_literals"]():
        tests.run("test/test_literals.mojo", test_literals.run_tests[True])
    comptime if module_selected["test_nfa"]():
        tests.run("test/test_nfa.mojo", test_nfa.run_tests[True])
    comptime if module_selected["test_public_api"]():
        tests.run("test/test_public_api.mojo", test_public_api.run_tests[True])
    comptime if module_selected["test_result_foundations"]():
        tests.run(
            "test/test_result_foundations.mojo",
            test_result_foundations.run_tests[True],
        )
    comptime if module_selected["test_simd_equivalence"]():
        tests.run(
            "test/test_simd_equivalence.mojo",
            test_simd_equivalence.run_tests[True],
        )
    comptime if module_selected["test_syntax"]():
        tests.run("test/test_syntax.mojo", test_syntax.run_tests[True])
    tests^.finish()
