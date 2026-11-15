(*
  Statement-only formalization of miniF2F test problem mathd_algebra_270: evaluating twice a
  real function given by the reciprocal of x + 2 away from -2. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory;

val mathd_algebra_270 =
  ``!f : real -> real.
      (!x : real. x <> -2 ==> f x = 1 / (x + 2))
      ==>
      f (f 1) = 3 / 7``;
