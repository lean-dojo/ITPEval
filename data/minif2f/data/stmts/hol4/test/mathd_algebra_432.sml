(*
  Statement-only formalization of miniF2F test problem mathd_algebra_432: expanding a product
  of linear real expressions gives the corresponding quadratic polynomial. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_432 =
  ``!x : real.
      (x + 3) * (2 * x - 6) = 2 * x pow 2 - 18``;
