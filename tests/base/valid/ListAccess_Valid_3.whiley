import * from whiley.lang.*

string f([int] x):
     return Any.toString(|x|)

void ::main(System.Console sys,[string] args):
     arr = [[1,2,3]]
     sys.out.println(f(arr[0]))
