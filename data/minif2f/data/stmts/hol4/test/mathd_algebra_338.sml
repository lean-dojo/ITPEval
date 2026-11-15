(*
  Statement-only formalization of miniF2F test problem mathd_algebra_338: a real three-variable
  linear system determines the product a * b * c. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_338 =
  ``!a b c : real.
      3 * a + b + c = -3 /\
      a + 3 * b + c = 9 /\
      a + b + 3 * c = 19
      ==>
      a * b * c = -56``;
