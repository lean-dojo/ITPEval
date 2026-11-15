(*
  Statement-only formalization of miniF2F test problem mathd_algebra_80: solving a rational
  equation over the reals under its nonzero-denominator assumption. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_80 =
  ``!x : real.
      x <> -1 /\
      (x - 9) / (x + 1) = 2
      ==>
      x = -11``;
