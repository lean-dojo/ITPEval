(*
  Statement-only formalization of miniF2F test problem mathd_algebra_419: evaluation of a real
  polynomial at a = -1 and b = 5. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_419 =
  ``!a b : real.
      a = -1 /\
      b = 5
      ==>
      -a - b pow 2 + 3 * (a * b) = -39``;
