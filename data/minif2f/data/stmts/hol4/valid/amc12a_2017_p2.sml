(*
  Statement-only formalization of miniF2F artifact amc12a_2017_p2: the reciprocal-sum identity
  for nonzero real numbers satisfying x + y = 4xy. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val amc12a_2017_p2 =
  ``!x y : real.
      x <> 0 /\
      y <> 0 /\
      x + y = 4 * (x * y)
      ==>
      1 / x + 1 / y = 4``;
