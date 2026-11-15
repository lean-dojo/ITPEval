(*
  Statement-only formalization of miniF2F artifact amc12a_2008_p8: positive real solutions of
  the given cubic and quadratic equations have x cubed equal to twice the square root of two.
  This file contains no proof.
*)

let statement =
  `!x y:real.
     (&0 < x /\ &0 < y) /\
     y pow 3 = &1 /\
     &6 * x pow 2 = &2 * (&6 * y pow 2)
     ==> x pow 3 = &2 * sqrt (&2)`;;
