import * from whiley.lang.*

int f(int|bool x):
    if x is int:
        return x
    else:
        return 1 

void ::main(System.Console sys,[string] args):
    sys.out.println(Any.toString(f(true)))
    sys.out.println(Any.toString(f(123)))
