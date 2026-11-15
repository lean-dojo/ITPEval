(*
  Statement-only formalization of miniF2F test problem mathd_algebra_114. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_114 =
  ``!a : real.
      a = 8
      ==>
      (16 * ((a pow 2) powr (1 / 3 : real))) powr (1 / 3 : real) = 4``;
