chan c=[0] of {int}

active proctype snd() {
  int sn=0;
  do
    :: c!sn; sn++
  od
}

active proctype rec() {
  int rn;
  do
    :: c?rn; printf("rec : %d\n", rn)
  od
}
