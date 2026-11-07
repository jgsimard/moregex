"""Run with `pixi run -e dev mojo run -I . benchmarks/bench_fallback.mojo`."""

from std.benchmark import keep
from std.time import perf_counter_ns
from moregex import Regex, count, matches, search
from moregex._plan import _COUNT_GENERIC, _SEARCH_GENERIC, _execution_plan


@no_inline
def public_search[regex: Regex](text: String) -> Int:
    return Int(search[regex](text))


@no_inline
def public_count[regex: Regex](text: String) -> Int:
    return count[regex](text)


@no_inline
def full[regex: Regex](text: String) -> Int:
    return Int(matches[regex](text))


def bench[regex: Regex, mode: Int](name: String, text: String, iterations: Int):
    var best = Float64(1e30)
    for _ in range(5):
        var start = perf_counter_ns()
        for _ in range(iterations):
            comptime if mode == 0:
                keep(public_search[regex](text))
            elif mode == 1:
                keep(public_count[regex](text))
            else:
                keep(full[regex](text))
        var elapsed = Float64(perf_counter_ns() - start) / Float64(iterations)
        best = min(best, elapsed)
    print(name, best, "ns/call (best of 5)")


def main():
    comptime r = Regex("[a-z]+[0-9]+[A-Z]+\\b")
    # This pattern reaches the shared generic scan in both public APIs.
    comptime plan = _execution_plan[r]()
    comptime assert plan.search_strategy == _SEARCH_GENERIC
    comptime assert plan.count_strategy == _COUNT_GENERIC
    var long_text = "a" * 4096 + "1" * 1024 + "END"
    var short_text = "abc123END"
    bench[r, 0]("search long", long_text, 10000)
    bench[r, 0]("search short", short_text, 100000)
    bench[r, 1]("count long", long_text, 2000)
    bench[r, 1]("count short", short_text, 100000)
    bench[r, 2]("matches long", long_text, 2000)
    bench[r, 2]("matches short", short_text, 100000)
