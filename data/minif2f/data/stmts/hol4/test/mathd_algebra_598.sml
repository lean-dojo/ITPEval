(*
  Statement-only formalization of miniF2F test problem mathd_algebra_598: a chain of four
  real-exponent equations determines the product of the exponents. This file contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val mathd_algebra_598 =
  ``!a b c d : real.
      4 powr a = 5 /\
      5 powr b = 6 /\
      6 powr c = 7 /\
      7 powr d = 8
      ==>
      a * b * c * d = 3 / 2``;
