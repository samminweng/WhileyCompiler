import * from whiley.lang.*

!null f(int x):
    return x

void ::main(System.Console sys, [string] args):
    sys.out.println(Any.toString(f(1)))


