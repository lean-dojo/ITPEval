(*
  Statement-only formalization of miniF2F test problem mathd_algebra_176: the real polynomial
  identity obtained by expanding (x + 1)^2 * x. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_176 =
  ``!x : real.
      (x + 1) pow 2 * x = x pow 3 + 2 * x pow 2 + x``;
