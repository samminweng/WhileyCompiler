import * from whiley.lang.*

define ilist as int | [int]
define rlist as real | [int]

string f(rlist e):
    if e is [int]:
        return "[int]"
    else:
        return "real"

string g(ilist e):
    return f(e)


void ::main(System.Console sys,[string] args):
    sys.out.println(f(1))
    sys.out.println(f([1]))
    sys.out.println(f([]))
