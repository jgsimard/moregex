from moregex import Regex


comptime UNSUPPORTED = Regex("a(?=b)")


def main():
    print(UNSUPPORTED.root)
