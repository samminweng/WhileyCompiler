import * from whiley.lang.*

int f(Type.nat x):
    return x-1

public void ::main(System.Console sys):
    sys.out.println(Any.toString(f(1)))
