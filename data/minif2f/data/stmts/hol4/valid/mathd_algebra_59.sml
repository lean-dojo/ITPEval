(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_59: a real exponential
  equation with base 4 determines its exponent. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_59 =
  ``!b : real.
      4 powr b + 2 pow 3 = 12
      ==>
      b = 1``;
