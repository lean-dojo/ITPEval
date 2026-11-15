(*
  Statement-only formalization of miniF2F test problem mathd_algebra_293: a product identity for
  square roots over nonnegative real numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_293 =
  ``!x : real.
      0 <= x ==>
      sqrt (60 * x) * sqrt (12 * x) * sqrt (63 * x) =
        36 * x * sqrt (35 * x)``;
