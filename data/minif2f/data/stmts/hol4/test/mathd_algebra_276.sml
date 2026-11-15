(*
  Statement-only formalization of miniF2F test problem mathd_algebra_276: integer coefficients
  in a real quadratic factorization determine an integer coefficient relation. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val mathd_algebra_276 =
  ``!a b : int.
      (!x : real.
         10 * x pow 2 - x - 24 =
           (real_of_int a * x - 8) * (real_of_int b * x + 3))
      ==>
      a * b + b = 12``;
