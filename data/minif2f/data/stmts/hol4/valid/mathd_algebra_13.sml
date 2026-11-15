(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_13:
  determining the real coefficients in a partial-fraction identity. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_13 =
  ``!a b : real.
      (!x : real.
          x - 3 <> 0 /\ x - 5 <> 0
          ==>
          4 * x / (x pow 2 - 8 * x + 15) =
            a / (x - 3) + b / (x - 5))
      ==>
      a = -6 /\ b = 10``;
