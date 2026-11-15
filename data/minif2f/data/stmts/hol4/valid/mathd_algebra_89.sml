(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_89: a reciprocal power
  identity for a nonzero real variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_89 =
  ``!b : real.
      b <> 0
      ==>
      (7 * b pow 3) pow 2 * (1 / ((4 * b pow 2) pow 3)) = 49 / 64``;
