(*
  Statement-only formalization of miniF2F test problem mathd_algebra_756: two
  real-exponentiation equations imply that the reversed power equals 243. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_756 =
  ``!a b : real.
      2 powr a = 32 /\
      a powr b = 125
      ==>
      b powr a = 243``;
