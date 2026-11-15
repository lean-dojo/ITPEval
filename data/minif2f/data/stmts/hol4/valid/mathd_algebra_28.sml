(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_28:
  bounding the constant term of a real quadratic that is nonpositive at some
  real input. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_28 =
  ``!c : real. !f : real -> real.
      (!x : real. f x = 2 * x pow 2 + 5 * x + c) /\
      (?x : real. f x <= 0)
      ==>
      c <= 25 / 8``;
