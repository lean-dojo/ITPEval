(*
  Statement-only formalization of miniF2F test problem mathd_algebra_139: evaluating a
  reciprocal-difference quotient on nonzero real inputs at 3 and 11. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_139 =
  ``!s : real -> real -> real.
      (!x y : real.
        ~(x = 0) /\ ~(y = 0)
        ==>
        s x y = ((1 : real) / y - 1 / x) / (x - y))
      ==>
      s 3 11 = (1 : real) / 33``;
