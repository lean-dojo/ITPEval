(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_55:
  evaluating two finite alternating sums of real numbers and their ratio.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_55 =
  ``!q p : real.
      (q = 2 - 4 + 6 - 8 + 10 - 12 + 14) /\
      (p = 3 - 6 + 9 - 12 + 15 - 18 + 21)
      ==>
      q / p = 2 / 3``;
