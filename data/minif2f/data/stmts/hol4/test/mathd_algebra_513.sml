(*
  Statement-only formalization of miniF2F test problem mathd_algebra_513: two real linear
  equations determine both variables. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_513 =
  ``!a b : real.
      3 * a + 2 * b = 5 /\
      a + b = 2
      ==>
      a = 1 /\ b = 1``;
