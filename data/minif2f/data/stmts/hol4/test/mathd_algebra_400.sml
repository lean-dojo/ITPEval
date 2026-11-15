(*
  Statement-only formalization of miniF2F test problem mathd_algebra_400: a real linear equation
  determines x. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_400 =
  ``!x : real.
      5 + 500 / 100 * 10 = 110 / 100 * x
      ==>
      x = 50``;
