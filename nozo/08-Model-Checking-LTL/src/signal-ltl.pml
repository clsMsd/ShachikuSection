mtype = {BLUE, RED, LOCKED, UNLOCKED};
mtype mutex1 = LOCKED;
mtype mutex2 = LOCKED;
mtype state1 = BLUE, state2 = RED;

inline lock(m) {
  d_step{m == UNLOCKED -> m = LOCKED}
}

inline unlock(m){
  m = UNLOCKED
}

active proctype signal1(){
  do
    :: state1 = RED;
       unlock(mutex2);
       lock(mutex1);
       state1 = BLUE
  od
}

active proctype signal2(){
  do
    :: lock(mutex2);
       state2 = BLUE;
       state2 = RED;
       unlock(mutex1)
  od
}

#define p state1 == BLUE
#define q state2 == BLUE

never  {    /* !([]!(p && q)) */
T0_init:
  do
    :: atomic { ((p && q)) -> assert(!((p && q))) }
    :: (1) -> goto T0_init
  od;
accept_all:
  skip
}
