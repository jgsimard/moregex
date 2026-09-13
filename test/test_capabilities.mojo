from std.testing import TestSuite, assert_equal, assert_false, assert_true

from moregex import (
    Regex,
    count,
    count_span,
    count_spans,
    count_spans_span,
    matches,
    matches_runtime,
    search,
)


def test_character_classes() raises:
    comptime identifier = Regex("[a-zA-Z_][a-zA-Z0-9_]*")
    assert_true(matches[identifier]("hello_123"))
    assert_true(matches[identifier]("_private"))
    assert_false(matches[identifier]("9lives"))
    assert_false(matches[identifier]("has-hyphen"))

    comptime negated = Regex("[^0-9]+")
    assert_true(matches[negated]("letters-only"))
    assert_false(matches[negated]("letters2"))

    comptime combined = Regex("[\\dA-F_]+")
    assert_true(matches[combined]("A19_F"))
    assert_false(matches[combined]("G19"))
    comptime any_byte_union = Regex("[\\s\\S]+")
    assert_true(matches[any_byte_union]("text\n123"))
    comptime non_digit = Regex("\\D+")
    assert_true(matches[non_digit]("abc !"))
    assert_false(matches[non_digit]("abc2"))
    comptime non_word = Regex("\\W+")
    assert_true(matches[non_word](" !\n"))
    assert_false(matches[non_word]("_"))
    comptime non_space = Regex("\\S+")
    assert_true(matches[non_space]("abc_123"))
    assert_false(matches[non_space]("abc 123"))


def test_case_insensitivity() raises:
    comptime folded_literal = Regex("Twain", case_insensitive=True)
    assert_true(matches[folded_literal]("tWaIn"))
    assert_true(search[folded_literal]("Mark TWAIN"))
    comptime folded_count = Regex("Sherlock Holmes", case_insensitive=True)
    var folded_haystack = "x" * 256 + "SHERLOCK HOLMES / sherlock holmes"
    assert_equal(count[folded_count](folded_haystack), 2)
    assert_equal(count_spans[folded_count](folded_haystack), 30)
    comptime folded_alternation = Regex(
        "Sherlock|Holmes|Watson", case_insensitive=True
    )
    var folded_alternation_text = "sHeRlOcK HOLMES watson"
    assert_equal(count[folded_alternation](folded_alternation_text), 3)
    assert_equal(count_spans[folded_alternation](folded_alternation_text), 20)
    comptime folded_run_alternation = Regex(
        "Sher[a-z]+|Hol[a-z]+", case_insensitive=True
    )
    assert_equal(count[folded_run_alternation]("xx SHERlock holMES! sher"), 2)
    assert_equal(
        count_spans[folded_run_alternation]("xx SHERlock holMES! sher"), 14
    )
    comptime folded_class = Regex("[a-f]+", case_insensitive=True)
    assert_true(matches[folded_class]("aBcDeF"))
    assert_false(matches[folded_class]("G"))
    comptime folded_negated = Regex("[^a]+", case_insensitive=True)
    assert_false(matches[folded_negated]("A"))
    assert_true(matches[folded_negated]("BCD"))


def test_groups_and_inline_flags() raises:
    comptime noncapturing = Regex("(?:ab|cd)+")
    assert_true(matches[noncapturing]("abcdab"))
    comptime scoped_dotall = Regex("(?s:.)+")
    assert_true(matches[scoped_dotall]("a\nb"))
    comptime global_dotall = Regex("(?s).+")
    assert_true(matches[global_dotall]("a\nb"))
    comptime global_dotall_star = Regex("(?s).*", unicode=True)
    assert_equal(count_spans[global_dotall_star]("a💩\n"), 6)
    assert_equal(count[global_dotall_star]("a💩\n"), 2)
    assert_equal(count[global_dotall_star](""), 1)
    comptime scoped_dotall_star = Regex("(?s:.*)", unicode=True)
    assert_equal(count_spans[scoped_dotall_star]("a💩\n"), 6)
    comptime scoped_fold = Regex("(?i:cat)")
    assert_true(matches[scoped_fold]("CAT"))
    comptime global_fold = Regex("(?i)cat")
    assert_true(matches[global_fold]("CaT"))
    comptime multiline = Regex("(?m)^cat$")
    assert_true(search[multiline]("dog\ncat\nfox"))
    assert_false(search[multiline]("dog\nscatter\nfox"))
    comptime multiline_whole_line = Regex("(?m)^.*$")
    assert_true(search[multiline_whole_line](""))
    assert_true(search[multiline_whole_line]("first\nsecond"))
    comptime scoped_multiline_whole_line = Regex("(?m:^.*$)")
    assert_true(search[scoped_multiline_whole_line]("first\nsecond"))
    comptime multiline_edges = Regex("(?m)^cat|cat$")
    assert_equal(count[multiline_edges]("catapult\nbobcat\nscatter\ncat"), 3)
    assert_equal(
        count_spans[multiline_edges]("catapult\nbobcat\nscatter\ncat"), 9
    )
    comptime end_anchor = Regex("$")
    assert_equal(count[end_anchor]("\n\n"), 2)


def test_ranges_and_quantifiers() raises:
    comptime hexadecimal_range = Regex("[x\\xE0-\\xFF]")
    assert_true(matches[hexadecimal_range]("x"))
    assert_false(matches[hexadecimal_range]("a"))
    comptime lazy_letters = Regex("[a-z]+?")
    assert_equal(count[lazy_letters]("abc"), 3)
    comptime bounded_letters = Regex("[A-Za-z]{2,3}")
    var bounded_letters_text = "abcd x abcdef"
    assert_equal(count[bounded_letters](bounded_letters_text), 3)
    assert_equal(count_spans[bounded_letters](bounded_letters_text), 9)
    comptime lazy_bounded_letters = Regex("[A-Za-z]{2,3}?")
    assert_equal(count[lazy_bounded_letters](bounded_letters_text), 5)
    assert_equal(count_spans[lazy_bounded_letters](bounded_letters_text), 10)
    comptime capitalized_words = Regex("(?:[A-Z][a-z]+\\s*){10,100}")
    var nine_words = "Word " * 9
    var ten_words = "Word " * 10
    var one_hundred_ten_words = "Word " * 110
    assert_equal(count[capitalized_words](nine_words), 0)
    assert_equal(count[capitalized_words](ten_words), 1)
    assert_equal(count_spans[capitalized_words](ten_words), 50)
    assert_equal(count[capitalized_words](one_hundred_ten_words), 2)
    assert_equal(count_spans[capitalized_words](one_hundred_ten_words), 550)
    comptime fixed_word_triplet = Regex("\\w{2}\\s\\w{3}\\s\\w{4}")
    assert_equal(count[fixed_word_triplet]("ab cde fghi! xx yyy zzzz"), 2)
    assert_equal(
        count_spans[fixed_word_triplet]("ab cde fghi! xx yyy zzzz"), 22
    )


def test_ordered_backtracking() raises:
    comptime nested_run = Regex("(a+)*[b-z]")
    assert_equal(count[nested_run]("aaaaaaaaaaaaaaaaaaaaaaaaa"), 0)
    assert_equal(count[nested_run]("aaabaaac"), 2)
    assert_equal(count_spans[nested_run]("aaabaaac"), 8)
    assert_equal(count_spans[nested_run]("aaa1aaab"), 4)
    comptime greedy_dot_complement = Regex(".*[^A-Z]|[A-Z]")
    assert_equal(count[greedy_dot_complement]("AAAA"), 4)
    assert_equal(count_spans[greedy_dot_complement]("AAAA"), 4)
    assert_equal(count[greedy_dot_complement]("AB!CD"), 3)
    assert_equal(count_spans[greedy_dot_complement]("AB!CD"), 5)
    assert_equal(count[greedy_dot_complement]("AB!CD?\nZZ"), 3)
    assert_equal(count_spans[greedy_dot_complement]("AB!CD?\nZZ"), 9)
    assert_equal(count[greedy_dot_complement](""), 0)
    comptime lazy_suffix = Regex("a+?b")
    assert_equal(count_spans[lazy_suffix]("aaab aab"), 7)
    comptime reconsidered_alternative = Regex("(a|aa)c")
    assert_true(search[reconsidered_alternative]("xxaac"))
    assert_equal(count[reconsidered_alternative]("aac ac"), 2)
    assert_equal(count_spans[reconsidered_alternative]("aac ac"), 5)
    comptime nested_giveback_suffix = Regex("(a+)*ab")
    assert_true(search[nested_giveback_suffix]("xxaaab"))
    assert_equal(count[nested_giveback_suffix]("aaab"), 1)
    assert_equal(count_spans[nested_giveback_suffix]("aaab"), 4)


def test_unicode() raises:
    comptime unicode_literal = Regex("Шерлок Холмс", unicode=True)
    assert_true(search[unicode_literal]("Это Шерлок Холмс."))
    var unicode_literal_haystack = (
        "Ш" * 2100 + "Шерлок Холмс" + "x" * 67 + "Шерлок Холмс"
    )
    assert_equal(count[unicode_literal](unicode_literal_haystack), 2)
    assert_equal(count_spans[unicode_literal](unicode_literal_haystack), 46)
    comptime unicode_alternation = Regex("∞|✓", unicode=True)
    assert_equal(count[unicode_alternation]("∞ x ✓"), 2)
    comptime byte_dot = Regex(".")
    comptime unicode_dot = Regex(".", unicode=True)
    assert_equal(count[byte_dot]("💩"), 4)
    assert_equal(count[unicode_dot]("a💩\n"), 2)
    assert_equal(count_spans[unicode_dot]("a💩\n"), 5)
    assert_equal(count[unicode_dot](""), 0)
    assert_equal(count_spans[unicode_dot](""), 0)
    assert_true(matches[unicode_dot]("💩"))
    comptime unicode_dotall_atom = Regex("(?s:.)", unicode=True)
    assert_equal(count[unicode_dotall_atom]("a💩\n"), 3)
    assert_equal(count_spans[unicode_dotall_atom]("a💩\n"), 6)
    assert_equal(count[unicode_dotall_atom](""), 0)
    comptime unicode_dotall = Regex("(?s:.)+", unicode=True)
    assert_equal(count[unicode_dotall]("a💩\n"), 1)
    assert_equal(count_spans[unicode_dotall]("a💩\n"), 6)
    assert_equal(count[unicode_dotall](""), 0)
    assert_equal(count_spans[unicode_dotall](""), 0)
    comptime unicode_backtracking = Regex(".+x", unicode=True)
    assert_true(matches[unicode_backtracking]("💩x"))
    assert_true(search[unicode_backtracking]("zz💩x"))
    assert_equal(count_spans[unicode_backtracking]("💩x 💩x"), 11)


def test_counted_repetitions() raises:
    comptime root_class = Regex("[ac]")
    assert_equal(count[root_class]("bbbca"), 2)
    assert_equal(count_spans[root_class]("bbbca"), 2)

    comptime exact_count = Regex("a{3}")
    assert_true(matches[exact_count]("aaa"))
    assert_false(matches[exact_count]("aa"))
    assert_false(matches[exact_count]("aaaa"))

    comptime bounded_count = Regex("ab{2,4}c")
    assert_true(matches[bounded_count]("abbc"))
    assert_true(matches[bounded_count]("abbbbc"))
    assert_false(matches[bounded_count]("abc"))
    assert_false(matches[bounded_count]("abbbbbc"))

    comptime open_count = Regex("x{2,}")
    assert_true(matches[open_count]("xx"))
    assert_true(matches[open_count]("xxxxxxxx"))
    assert_false(matches[open_count]("x"))

    comptime long_unbounded_word = Regex("\\w{10,}")
    assert_equal(count[long_unbounded_word]("abcdef"), 0)
    var long_unbounded_text = "short abcdefghij abcdefghijkl"
    assert_equal(count[long_unbounded_word](long_unbounded_text), 2)
    assert_equal(count_spans[long_unbounded_word](long_unbounded_text), 22)
    comptime lazy_unbounded_word = Regex("\\w{3,}?")
    assert_equal(count[lazy_unbounded_word]("abcdef ghijk"), 3)
    assert_equal(count_spans[lazy_unbounded_word]("abcdef ghijk"), 9)


def test_literal_search_and_alternation() raises:
    comptime cat = Regex("cat")
    assert_true(search[cat]("a cat naps"))
    assert_true(search[cat]("concatenate"))
    assert_false(search[cat]("dogs"))
    assert_false(matches[cat]("a cat naps"))

    comptime animals = Regex("cat|dog|fox|horse")
    assert_true(search[animals]("cat naps"))
    assert_true(search[animals]("a dog naps"))
    assert_true(search[animals]("the quick fox"))
    assert_true(search[animals]("one horse"))
    assert_false(search[animals]("no animals here"))
    assert_true(search[animals]("x" * 63 + "horse"))
    assert_true(search[animals]("c" * 64 + "cat"))
    assert_false(search[animals]("x" * 64 + "hors"))

    comptime aws_key = Regex("((?:ASIA|AKIA|AROA|AIDA)([A-Z0-7]{16}))")
    assert_true(search[aws_key]("prefix AKIA01234567ABCDEFGH suffix"))
    assert_true(search[aws_key]("x" * 63 + "AROAABCDEFGH01234567"))
    assert_true(search[aws_key]("x" * 62 + "AROAABCDEFGH01234567"))
    assert_true(search[aws_key]("x" * 30 + "AROAABCDEFGH01234567"))
    assert_true(search[aws_key]("x" * 14 + "AROAABCDEFGH01234567"))
    assert_true(search[aws_key]("x" * 6 + "AROAABCDEFGH01234567"))
    assert_true(search[aws_key]("x" * 2 + "AROAABCDEFGH01234567"))
    assert_true(search[aws_key]("AIDAABCDEFGH01234567"))
    assert_false(search[aws_key]("ASIA0123456789ABCDEF"))
    assert_false(search[aws_key]("ASIA01234567ABCDEFG"))
    assert_false(search[aws_key]("XSIA01234567ABCDEFGH"))
    comptime unequal_prefix_widths = Regex("(ACDE|AB)[0-7]{2}")
    assert_true(search[unequal_prefix_widths]("AB07"))
    assert_true(search[unequal_prefix_widths]("ACDE07"))
    assert_false(search[unequal_prefix_widths]("AB08"))
    comptime no_common_last = Regex("(AB|AC)[0-7]{2}")
    assert_true(search[no_common_last]("prefix AC07 suffix"))
    assert_false(search[no_common_last]("prefix AD07 suffix"))

    comptime shared_prefix = Regex("catastrophe|catapult|category|caterpillar")
    assert_true(search[shared_prefix]("a category appears"))
    assert_false(search[shared_prefix]("a cat appears"))


def test_anchors() raises:
    comptime at_start = Regex("^cat")
    assert_true(search[at_start]("cat naps"))
    assert_false(search[at_start]("a cat naps"))

    comptime at_end = Regex("cat$")
    assert_true(search[at_end]("a cat"))
    assert_false(search[at_end]("cat naps"))
    comptime class_literal_end = Regex("[cd]at$")
    assert_equal(count_spans[class_literal_end]("xcat"), 3)
    assert_equal(count_spans[class_literal_end]("xcat\n"), 3)
    assert_equal(count[class_literal_end]("xbat"), 0)

    comptime exact = Regex("^cat$")
    assert_true(search[exact]("cat"))
    assert_false(search[exact]("a cat"))
    assert_equal(count[exact]("catcat"), 0)
    assert_equal(count_spans[exact]("cat"), 3)
    comptime bounded_exact = Regex("^a{2,5}$")
    assert_equal(count[bounded_exact]("a" * 10000), 0)
    assert_equal(count_spans[bounded_exact]("aaaa"), 4)
    comptime alternative_exact = Regex("^((aaa)|(aa))$")
    assert_equal(count[alternative_exact]("a" * 10000), 0)
    assert_equal(count_spans[alternative_exact]("aaa"), 3)
    assert_equal(count_spans[alternative_exact]("aa\n"), 2)


def test_word_boundaries() raises:
    comptime word = Regex("\\bcat\\b")
    assert_true(search[word]("a cat!"))
    assert_false(search[word]("scatter"))
    assert_false(search[word]("_cat_"))
    comptime keyword_words = Regex("\\b(cat|dog)\\b")
    var keyword_text = "cat dog scatter dogcat dog"
    assert_equal(count[keyword_words](keyword_text), 3)
    assert_equal(count_spans[keyword_words](keyword_text), 9)
    comptime nonword_boundary_start = Regex("\\b-cat\\b")
    assert_equal(count[nonword_boundary_start]("x-cat plain -cat"), 1)
    comptime mixed_boundary_start = Regex("\\b(cat|-dog)\\b")
    assert_equal(count[mixed_boundary_start]("cat x-dog plain -dog"), 2)

    comptime inside_word = Regex("\\Bcat\\B")
    assert_true(search[inside_word]("scatter"))
    assert_false(search[inside_word]("cat"))

    comptime long_word = Regex("\\b\\w{25,}\\b")
    assert_true(search[long_word]("short " + "x" * 25 + "!"))
    assert_false(search[long_word]("short " + "x" * 24 + "!"))
    assert_true(search[long_word]("1234567890_abcdefghijklmno"))
    assert_equal(count[long_word]("short " + "x" * 25 + " " + "y" * 26), 2)
    assert_equal(
        count_spans[long_word]("short " + "x" * 25 + " " + "y" * 26), 51
    )
    comptime bracket_long_word = Regex("\\b[0-9A-Za-z_]{12,}\\b")
    assert_equal(
        count_spans[bracket_long_word]("tiny abcdefghijk_ 123456789012"), 24
    )
    var crossing_long_word = "!" * 63 + "x" * 25 + "!"
    assert_equal(count[long_word](crossing_long_word), 1)
    assert_equal(count_spans[long_word](crossing_long_word), 25)
    assert_equal(count_spans[long_word]("x" * 64 + "!" + "y" * 129), 193)


def test_structured_patterns() raises:
    comptime numeric_date = Regex(
        "([0-9][0-9]?)/([0-9][0-9]?)/([0-9][0-9]([0-9][0-9])?)"
    )
    assert_true(search[numeric_date]("published 9/3/26"))
    assert_true(search[numeric_date]("published 09/03/2026"))
    assert_false(search[numeric_date]("published 09/333/2026"))
    assert_false(search[numeric_date]("published 09/03/x026"))
    assert_true(search[numeric_date]("x" * 63 + "1/2/34"))
    assert_true(search[numeric_date]("x" * 62 + "1/2/34"))
    assert_true(search[numeric_date]("x" * 30 + "1/2/34"))
    assert_true(search[numeric_date]("x" * 14 + "1/2/34"))
    assert_true(search[numeric_date]("x" * 6 + "1/2/34"))
    assert_true(search[numeric_date]("x" * 2 + "1/2/34"))

    comptime ipv4 = Regex(
        "(?:(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9])\\.){3}"
        "(?:25[0-5]|2[0-4][0-9]|[01]?[0-9][0-9])"
    )
    var ipv4_text = "x999.168.00.01 192.168.00.01 01.02.03.04"
    assert_equal(count[ipv4](ipv4_text), 3)
    assert_equal(count_spans[ipv4](ipv4_text), 36)
    assert_equal(count_spans[ipv4]("0000.00.00.00"), 12)
    assert_equal(count_spans[ipv4]("250.249.199.99"), 14)
    assert_equal(count_spans[ipv4]("256.249.199.99"), 13)


def test_escapes_and_dot() raises:
    comptime escaped = Regex("\\^\\$\\[\\]\\{\\}")
    assert_true(matches[escaped]("^$[]{}"))
    comptime control_escapes = Regex("a\\nb\\tc\\r")
    assert_true(matches[control_escapes]("a\nb\tc\r"))
    comptime not_newline = Regex("[^\\n]+")
    assert_true(matches[not_newline]("abc"))
    assert_false(matches[not_newline]("a\nb"))
    comptime dot = Regex(".+")
    assert_true(matches[dot]("abc"))
    assert_false(matches[dot]("a\nb"))


def test_greedy_and_delimited_patterns() raises:
    comptime greedy_suffix = Regex("\\b\\w+nn\\b")
    assert_true(search[greedy_suffix]("Finn went home"))
    assert_equal(count[greedy_suffix]("nn Finn Ann nnn xnnx"), 3)
    assert_equal(count_spans[greedy_suffix]("nn Finn Ann nnn xnnx"), 10)
    comptime bounded_suffix = Regex("Tom.{2,5}river")
    assert_true(search[bounded_suffix]("Tom by river"))
    comptime adjacent_dot_stars = Regex(".*.*=.*")
    var redos_lines = "x=" + "x" * 10_000 + "\nno match\ny=z"
    assert_equal(count[adjacent_dot_stars](redos_lines), 2)
    assert_equal(count_spans[adjacent_dot_stars](redos_lines), 10_005)
    comptime repeated_delimiter = Regex("(.*?,){13}z")
    var delimiter_match = "a," * 13 + "z"
    assert_equal(
        count[repeated_delimiter](delimiter_match + "\n" + delimiter_match), 2
    )
    assert_equal(
        count_spans[repeated_delimiter](
            delimiter_match + "\n" + delimiter_match
        ),
        2 * delimiter_match.byte_length(),
    )
    assert_equal(count[repeated_delimiter]("a," * 12 + "z"), 0)
    var delimiter_vector_text = "x" * 37 + delimiter_match + "x" * 64
    assert_equal(count[repeated_delimiter](delimiter_vector_text), 1)
    assert_equal(count_spans[repeated_delimiter](delimiter_vector_text), 64)
    var delimiter_boundary_text = "x" * 38 + delimiter_match + "x" * 64
    assert_equal(count[repeated_delimiter](delimiter_boundary_text), 1)
    comptime prefixed_nested_dot = Regex(
        "(?:foo|bar)+[)]*;?(?:!|-)*.*(?:.*=.*)"
    )
    var prefixed_nested_text = "none=bad\nbar);!- x=ok"
    assert_equal(count[prefixed_nested_dot](prefixed_nested_text), 1)
    assert_equal(count_spans[prefixed_nested_dot](prefixed_nested_text), 12)


def test_anchored_and_reverse_infix() raises:
    comptime anchored_suffix = Regex("[ -~]*ABCDEFGHIJKLMNOPQRSTUVWXYZ$")
    assert_equal(
        count_spans[anchored_suffix]("abc\nxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"), 29
    )
    comptime trailing_dot = Regex("[ -~]*ABCDEFGHIJKLMNOPQRSTUVWXYZ.*")
    assert_equal(
        count_spans[trailing_dot]("abc\nxyzABCDEFGHIJKLMNOPQRSTUVWXYZ!"), 30
    )
    comptime fixed_end = Regex("[A-Z]xyz$")
    assert_equal(count_spans[fixed_end]("a" * 1000 + "Xxyz"), 4)
    assert_equal(count_spans[fixed_end]("a" * 1000 + "xyzz"), 0)

    comptime reverse_infix = Regex("\\b\\w+\\s+Holmes\\s+\\w+\\b")
    assert_equal(count_spans[reverse_infix]("Mr Sherlock Holmes said"), 20)
    comptime bounded_infix = Regex("\\s[a-zA-Z]{0,12}ing\\s")
    assert_equal(count_spans[bounded_infix](" is walking home "), 9)
    comptime bounded_context = Regex(
        "[A-Za-z]{10}\\s+[\\s\\S]{0,100}Result[\\s\\S]{0,100}\\s+[A-Za-z]{10}"
    )
    var greedy_context = (
        "abcdefghij Result parenthese Result" + "x" * 90 + " klmnopqrst"
    )
    assert_equal(count[bounded_context](greedy_context), 1)
    assert_equal(
        count_spans[bounded_context](greedy_context),
        greedy_context.byte_length(),
    )
    comptime run_suffix = Regex("[a-zA-Z]+ing")
    assert_equal(count_spans[run_suffix]("walking sing singing"), 18)
    assert_equal(count_spans[run_suffix]("singalong"), 4)
    comptime reverse_suffix_class = Regex(".efg[a-z]+[A-Z]")
    assert_equal(count_spans[reverse_suffix_class]("xefgabcZ"), 8)
    assert_equal(count_spans[reverse_suffix_class]("xefgabc"), 0)


def test_bounded_alternations() raises:
    comptime bounded_alternation = Regex(".{0,2}(Tom|Sawyer|Finn)")
    assert_equal(count[bounded_alternation]("xxTom yyFinn"), 2)
    assert_equal(count_spans[bounded_alternation]("xxTom\nzzSawyer"), 13)
    assert_equal(count[bounded_alternation]("Tom Sawyer"), 2)
    assert_equal(count_spans[bounded_alternation]("Tom Sawyer"), 10)
    comptime long_bounded_alternation = Regex(
        ".{2,4}(Tom|Sawyer|Huckleberry|Finn)"
    )
    assert_equal(count[long_bounded_alternation]("xxxxTom xxSawyer"), 2)
    assert_equal(count_spans[long_bounded_alternation]("xxxxTom xxSawyer"), 16)
    assert_equal(count[long_bounded_alternation]("Tom\nxFinn\nxxFinn"), 1)
    var bounded_vector_text = "x" * 63 + "Huckleberry" + "z" * 64
    assert_equal(count[long_bounded_alternation](bounded_vector_text), 1)
    assert_equal(count_spans[long_bounded_alternation](bounded_vector_text), 15)
    comptime digit_bounded_alternation = Regex("[0-9]{2,4}(Tom|Finn)")
    assert_equal(count[digit_bounded_alternation]("1234Tom x12Finn"), 2)
    assert_equal(count[digit_bounded_alternation]("1Tom xxFinn"), 0)
    comptime class_literal_alternation = Regex("([A-Za-z]awyer|[A-Za-z]inn)\\s")
    assert_equal(count[class_literal_alternation]("Sawyer Finn Hinnx"), 2)
    assert_equal(
        count_spans[class_literal_alternation]("Sawyer Finn Hinnx"), 12
    )
    assert_equal(
        count[class_literal_alternation](
            "Xaxxxr Xixn Xawyer\x00 Yinn\x0b Sawyer Finn "
        ),
        2,
    )
    var class_literal_vector_text = "x" * 63 + "Sawyer " + "x" * 64
    assert_equal(count[class_literal_alternation](class_literal_vector_text), 1)
    comptime distinct_class_literal_alternation = Regex(
        "([A-Z]awyer|[a-z]inn)\\s"
    )
    assert_equal(
        count[distinct_class_literal_alternation]("Sawyer finn sawyer Finn"), 2
    )
    comptime bounded_quotes = Regex("[\"'][^\"']{0,3}[?!.][\"']")
    assert_equal(count[bounded_quotes]("\"Hi!\" and 'No?'"), 2)
    assert_equal(count_spans[bounded_quotes]("\"Hi!\" and 'No?'"), 10)


def test_literal_counting() raises:
    comptime repeated_literal = Regex("aba")
    assert_equal(count_spans[repeated_literal]("ababa aba"), 6)
    assert_equal(count[repeated_literal]("ababa aba"), 2)
    comptime one_byte_literal = Regex("y")
    assert_equal(count[one_byte_literal]("xyyyx"), 3)
    assert_equal(count_spans[one_byte_literal]("xyyyx"), 3)
    comptime long_literal = Regex("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
    assert_equal(
        count_spans[long_literal]("x" * 32 + "ABCDEFGHIJKLMNOPQRSTUVWXYZ"), 26
    )
    assert_equal(
        count[long_literal]("A" * 32 + "ABCDEFGHIJKLMNOPQRSTUVWXYZ"), 1
    )
    assert_equal(
        count_spans[long_literal](
            "ABCDEFGHIJKLMNOPQRSTUVWXYZxxxxxABCDEFGHIJKLMNOPQRSTUVWXYZ"
        ),
        52,
    )
    assert_equal(
        count[long_literal]("x" * 31 + "ABCDEFGHIJKLMNOPQRSTUVWXYx"), 0
    )
    var large_literal_haystack = (
        "x" * 4096
        + "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
        + "x" * 100
        + "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    )
    assert_equal(count[long_literal](large_literal_haystack), 2)
    assert_equal(count_spans[long_literal](large_literal_haystack), 52)
    var dense_literal_haystack = "aba" * 1400
    assert_equal(count[repeated_literal](dense_literal_haystack), 1400)
    assert_equal(count_spans[repeated_literal](dense_literal_haystack), 4200)
    comptime overlapping_literal = Regex("aa")
    var overlapping_haystack = "a" * 4097
    assert_equal(count[overlapping_literal](overlapping_haystack), 2048)
    assert_equal(count_spans[overlapping_literal](overlapping_haystack), 4096)
    comptime empty = Regex("")
    assert_equal(count[empty]("abc"), 4)
    var borrowed_text = String("cat dog cat")
    comptime pets = Regex("cat|dog")
    assert_equal(
        count_spans_span[pets](
            borrowed_text[byte = 0 : borrowed_text.byte_length()]
        ),
        9,
    )
    assert_equal(
        count_span[pets](borrowed_text[byte = 0 : borrowed_text.byte_length()]),
        3,
    )


def test_counting_execution_plans() raises:
    # Long enough to exercise the vectorized fixed-width iterator, including
    # non-overlapping advancement across SIMD block boundaries.
    comptime fixed_sequence = Regex("[a-z][^x]{2}x")
    var fixed_text = "abbx" * 80
    assert_equal(count_spans[fixed_sequence](fixed_text), 320)

    # A failed suffix candidate can overlap the next successful candidate.
    comptime overlapping_suffix = Regex("[b]aa")
    assert_equal(count_spans[overlapping_suffix]("cbaaa"), 3)

    comptime overlapping_alternatives = Regex("aa|a")
    assert_equal(count_spans[overlapping_alternatives]("aaa " * 40), 120)

    comptime prefixed_sequence = Regex("ab\\s+c")
    assert_equal(count_spans[prefixed_sequence]("xx ab c ab   c"), 10)

    comptime prefixed_alternation = Regex("ab[a-z]+|cd[0-9]+")
    assert_equal(count_spans[prefixed_alternation]("abz! cd12 abz"), 10)

    # Exercise the large-input greedy-run/literal-suffix kernel.  Each chunk
    # has four matches spanning 7, 4, 7, and 4 bytes respectively.
    comptime run_literal_suffix = Regex("[a-zA-Z]+ing")
    var run_suffix_text = "walking sing singing singalong " * 3000
    assert_equal(count[run_literal_suffix](run_suffix_text), 12000)
    assert_equal(count_spans[run_literal_suffix](run_suffix_text), 66000)

    comptime bounded_gap_alternation = Regex("Tom.{2,4}river|river.{2,4}Tom")
    assert_equal(
        count[bounded_gap_alternation]("Tom by river; river xx Tom"), 2
    )
    assert_equal(
        count_spans[bounded_gap_alternation]("Tom by river; river xx Tom"), 24
    )

    var runtime = Regex("[a-z]{2}")
    assert_true(matches_runtime(runtime, "az"))


def main() raises:
    TestSuite.discover_tests[__functions_in_module()]().run()
