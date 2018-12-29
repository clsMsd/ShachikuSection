#define N 4
int x = N;

ltl qq { <>([](x < N)) }

active proctype A() {
  do
    :: x%2==1 -> x = 3*x+1
  od
}

active proctype B() {
  do
    :: x%2==0 -> x = x/2
  od
}
