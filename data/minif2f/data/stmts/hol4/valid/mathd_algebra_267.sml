(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_267: a rational equation
  over the reals, with excluded denominator roots, implies x = 0. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_267 =
  ``!x : real.
      x <> 1 /\
      x <> -2 /\
      (x + 1) / (x - 1) = (x - 2) / (x + 2)
      ==>
      x = 0``;
