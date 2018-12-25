active proctype p() {
  int x=0;

  do
    :: x < 5 -> x++
    :: else  -> break
  od;

  printf("%d\n", x);
}