# moregex

An experimental regex matcher for Mojo. Constant patterns are parsed and
specialized at compile time; matching uses byte views, SIMD kernels, and an
ordered Thompson/Pike NFA for patterns that require alternative reconsideration
or greedy/lazy giveback.

Inspired by Evan Ovadia's [compile-time regex experiment](https://verdagon.dev/blog/impossible-optimization).

## Usage

```mojo
from moregex import Regex, count, finditer, matches, search

def main() raises:
    comptime email = Regex("\\w+@\\w+\\.\\w+")
    print(matches[email]("user@example.com"))

    comptime pets = Regex("cat|dog")
    print(search[pets]("a cat naps"))
    print(count[pets]("cat dog cat"))

    comptime placeholder = Regex("\\{\\{(.*?)\\}\\}")
    var template = "<h1>{{ TITLE }}</h1>"
    for found in finditer[placeholder](template):
        print(found.start(), found.end(), found.group(template, 1))
```

`matches` requires a full-string match; `search` tests for a match anywhere.
`find` returns the next `RegexMatch`, and `finditer` collects leftmost,
non-overlapping matches. Offsets are byte positions; up to 32 numbered capture
groups are supported, with strings copied on demand by `group(text, index)`.
`count` counts matches; `count_spans` sums their byte lengths. The `_span`
variants accept borrowed `ImmStringSpan` input (`count_span` counts matches).

Use `comptime regex = Regex("pattern")`; matching APIs take it as a compile-time
parameter. Invalid or unsupported patterns abort with an `invalid regex`
diagnostic, causing compilation to fail for `comptime` values.

## Syntax and limits

Supports literals, `.`, ASCII classes (`\d`, `\w`, `\s` and complements),
bracket classes and ranges, alternation, capturing/noncapturing groups,
greedy/lazy `?`, `*`, `+`, and counted repetition. Assertions include `^`, `$`
(also before a final line feed), and ASCII `\b`/`\B`. Global and scoped
`i`, `s`, and `m` flags enable ASCII case folding, dotall, and multiline mode.

Matching is byte-oriented by default. Exact UTF-8 literals work;
`unicode=True` makes dot consume a complete code point. Classes, folding, and
boundaries remain ASCII. There are no Unicode properties, look-around,
backreferences, or runtime-compiled patterns. Unsupported syntax and NFA-required
repetitions exceeding the 256-copy expansion limit are rejected during parsing.

## Development

The Pixi lockfile pins Mojo. Run `pixi install` to create the environment.

```bash
pixi run test                      # runtime suite and expected compile failures
pixi run test test/test_find.mojo   # select a module or directory
pixi run fmt                       # format source and tests
pixi run check                     # check formatting and run tests
```

Register new runtime modules in `test/run_tests.mojo` with a parameterized
`run_tests` entry point. Negative compilation tests live in `test/compile_fail/`.
