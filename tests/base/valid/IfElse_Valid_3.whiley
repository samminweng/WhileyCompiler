import * from whiley.lang.*

int f(int x):
    if(x < 10):
        return 1
    else:
        return 2

void ::main(System.Console sys,[string] args):
    sys.out.println(Any.toString(f(1)))
    sys.out.println(Any.toString(f(10)))
    sys.out.println(Any.toString(f(11)))
    sys.out.println(Any.toString(f(1212)))
    sys.out.println(Any.toString(f(-1212)))
