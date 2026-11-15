(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_410: the lower bound of a
  quadratic expression in a real variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_410 =
  ``!x y : real.
      y = x pow 2 - 6 * x + 13
      ==>
      4 <= y``;
