import * from whiley.lang.*

[int] f(string x):
    return x

void ::main(System.Console sys,[string] args):
    sys.out.println(Any.toString(f("Hello World")))