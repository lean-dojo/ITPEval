(*
  Statement-only formalization of miniF2F valid problem amc12b_2003_p17: a logarithmic system
  over positive real variables determines ln (x * y) as 3 / 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val amc12b_2003_p17 =
  ``!x y : real.
      0 < x /\
      0 < y /\
      ln (x * y pow 3) = 1 /\
      ln (x pow 2 * y) = 1
      ==>
      ln (x * y) = 3 / 5``;
