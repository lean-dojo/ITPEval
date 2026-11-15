(*
  Statement-only formalization of miniF2F test problem mathd_algebra_441: a rational real
  expression in a nonzero variable evaluates to 10. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_441 =
  ``!x : real.
      ~(x = 0)
      ==>
      12 / (x * x) * (x pow 4 / (14 * x)) * (35 / (3 * x)) = 10``;
