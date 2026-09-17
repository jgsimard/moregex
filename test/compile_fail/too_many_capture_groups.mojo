"""This fixture must fail while constructing a 33-group regex."""

from moregex import Regex


comptime UNSUPPORTED = Regex(
    "((a)(b)(c)(d)(e)(f)(g)(h)"
    "(i)(j)(k)(l)(m)(n)(o)(p)"
    "(q)(r)(s)(t)(u)(v)(w)(x)"
    "(y)(z)(A)(B)(C)(D)(E)(F))"
)


def main():
    print(UNSUPPORTED.root)
