(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_568: a polynomial identity
  in one real variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_568 =
  ``!a : real.
      (a - 1) * (a + 1) * (a + 2) - (a - 2) * (a + 1) =
      a pow 3 + a pow 2``;
