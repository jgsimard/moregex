from moregex import Regex


comptime UNSUPPORTED = Regex("(a|aa){257}suffix")


def main():
    print(UNSUPPORTED.root)
