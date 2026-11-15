(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2001_b2:
  the nonzero real solutions of the stated reciprocal polynomial system
  consist exactly of the pair determined by the positive fifth root of 3.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val putnam_2001_b2 =
  ``!x y : real.
      ~(x = 0) /\ ~(y = 0)
      ==>
      let r = (3 : real) powr (1 / 5)
      in
        (1 / x + 1 / (2 * y) =
           (x pow 2 + 3 * y pow 2) * (3 * x pow 2 + y pow 2) /\
         1 / x - 1 / (2 * y) =
           2 * (y pow 4 - x pow 4)
         <=>
         x = (r + 1) / 2 /\ y = (r - 1) / 2)``;
