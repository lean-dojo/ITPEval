(*
  miniF2F valid artifact mathd_algebra_480: a piecewise real function equals
  -x^2 - 1 below 0, equals 2 on [0,4), and equals sqrt(x) from 4 onward;
  its value at pi is 2. This is a statement-only formalization and contains
  no proof.
*)

needs "Library/transc.ml";;

let statement =
  `!f:real->real.
     (!x:real. x < &0 ==> f x = --(x pow 2) - &1) /\
     (!x:real. (&0 <= x /\ x < &4) ==> f x = &2) /\
     (!x:real. &4 <= x ==> f x = sqrt x)
     ==> f pi = &2`;;
