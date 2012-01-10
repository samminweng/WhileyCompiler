import * from whiley.lang.*

string f({int} xs, {int} ys, {int} zs):
    if zs == xs ∪ ys:
        return Any.toString(xs)
    else:
        return "FAILED"

string g({int} ys):
    return f(ys,ys,ys)

string h({int} ys, {int} zs):
    return f(ys,zs,ys ∪ zs)

void ::main(System.Console sys,[string] args):
    sys.out.println(g({}))
    sys.out.println(g({2}))
    sys.out.println(g({1,2,3}))
    sys.out.println(h({},{}))
    sys.out.println(h({1},{2}))
    sys.out.println(h({1,2,3},{3,4,5}))
