bool x = false;

ltl p1 {
  []((<>!x) && (<>x))
}

active proctype p() {
  do
  :: x = !x
  od
}
