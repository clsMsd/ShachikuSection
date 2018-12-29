mtype = {p, v};
chan S = [0] of {mtype};

active proctype sem() {
  do
    :: S?p; S?v
  od
}

proctype c1() {
  do
    :: S!p;
progress:
       /* do something */
       S!v
  od
}

proctype c2() {
  do
    :: S!p;
       /* do something */
       S!v
  od
}

init {
  run c1(); run c2()
}