proctype gcd(int x, y) {
  do
    :: x > y -> x = x - y
    :: x < y -> y = y - x
    :: else -> break
  od;
  printf("%d %d\n", x, y)
}

init { run gcd (72,16) }
