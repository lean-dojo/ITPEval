(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_101: a real quadratic
  inequality implies the bounds -2 <= x <= 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_101 =
  ``!x : real.
      x pow 2 - 5 * x - 4 <= 10
      ==>
      x >= -2 /\ x <= 7``;
