import println from whiley.lang.System

type sr3nat is int

method main(System.Console sys) => void:
    x = [1]
    x[0] = 1
    sys.out.println(Any.toString(x))