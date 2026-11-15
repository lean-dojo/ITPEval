(*
  Statement-only formalization of miniF2F valid problem mathd_algebra_109: solving a real linear
  equation after fixing one variable. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_109 =
  ``!a b : real.
      3 * a + 2 * b = 12 /\
      a = 4
      ==>
      b = 0``;
