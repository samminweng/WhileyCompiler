import * from whiley.lang.*

int f(int x, int y):
    a = x == y
    if(a):
        return 1
    else:
        return x + y

int g(int x, int y):
    a = x >= y
    if(!a):
        return x + y
    else:
        return 1


void ::main(System.Console sys,[string] args):
    sys.out.println(Any.toString(f(1,1)))
    sys.out.println(Any.toString(f(0,0)))
    sys.out.println(Any.toString(f(4,345)))
    sys.out.println(Any.toString(g(1,1)))
    sys.out.println(Any.toString(g(0,0)))
    sys.out.println(Any.toString(g(4,345)))
