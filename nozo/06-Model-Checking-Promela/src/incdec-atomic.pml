#define N 5
int x = 0;

active proctype inc() {
  do
    :: atomic{x < N -> x++}
  od
}

active proctype dec() {
  do
    :: atomic{x > 0 -> x--}
  od
}

active proctype reset() {
  do
    :: atomic{x == N -> x = 0}
  od
}

active proctype check() {
  assert (x >= 0 && x <= N)
}
