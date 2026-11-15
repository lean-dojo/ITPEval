(*
  Statement-only formalization of miniF2F test artifact mathd_algebra_113: the real quadratic
  x^2 - 14*x + 3 is minimized at x = 7. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_113 =
  ``!x : real.
      7 pow 2 - 14 * 7 + 3 <= x pow 2 - 14 * x + 3``;
