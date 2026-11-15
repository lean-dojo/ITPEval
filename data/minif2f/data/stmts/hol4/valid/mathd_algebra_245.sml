(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_245: a reciprocal and
  power identity for a nonzero real variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_245 =
  ``!x : real.
      x <> 0
      ==>
      1 / (4 / x) *
          ((3 * x pow 3) / x) pow 2 *
          (1 / (1 / (2 * x))) pow 3 =
        18 * x pow 8``;
