import * from whiley.lang.*

define nat as int
void ::main(System.Console sys,[string] args):
    xs = [1,2,3]
    r = 0
    for x in xs:
        r = r + x    
    sys.out.println(Any.toString(r))
