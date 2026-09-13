"""This fixture must fail while constructing a 17-group regex."""

from moregex import Regex


comptime UNSUPPORTED = Regex(
    "(a)(b)(c)(d)(e)(f)(g)(h)(i)(j)(k)(l)(m)(n)(o)(p)(q)"
)


def main():
    print(UNSUPPORTED.root)
