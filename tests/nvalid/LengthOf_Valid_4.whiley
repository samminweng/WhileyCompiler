import println from whiley.lang.System

type listsetdict is [int] | {int} | {int=>int}

function len(listsetdict l) => int:
    return |l|

method main(System.Console sys) => void:
    l = {1, 2, 3}
    sys.out.println(len(l))
    l = [1, 2]
    sys.out.println(len(l))
    l = {1=>2, 3=>4, 5=>6, 7=>8}
    sys.out.println(len(l))