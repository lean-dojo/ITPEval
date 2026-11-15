(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_433: evaluating at 8 a
  real function defined using a square root. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_433 =
  ``!f : real -> real.
      (!x : real. f x = 3 * sqrt (2 * x - 7) - 8)
      ==>
      f 8 = 1``;
