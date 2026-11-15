(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_480: evaluating at pi a
  real piecewise function that is constant at 2 on the interval 0 <= x < 4. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_480 =
  ``!f : real -> real.
      (!x : real. x < 0 ==> f x = ~(x pow 2) - 1) /\
      (!x : real. 0 <= x /\ x < 4 ==> f x = 2) /\
      (!x : real. 4 <= x ==> f x = sqrt x)
      ==>
      f pi = 2``;
