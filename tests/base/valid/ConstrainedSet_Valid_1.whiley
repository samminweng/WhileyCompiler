import * from whiley.lang.*

{int} f(int x):
    return {x}

void ::main(System.Console sys,[string] args):
    bytes = f(0)
    sys.out.println(Any.toString(bytes))

