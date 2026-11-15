(*
  Statement-only formalization of miniF2F test problem mathd_algebra_329: two real linear
  equations imply the value of x + y. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_329 =
  ``!x y : real.
      3 * y = x /\
      2 * x + 5 * y = 11
      ==>
      x + y = 4``;
