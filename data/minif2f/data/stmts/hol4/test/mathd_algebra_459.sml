(*
  Statement-only formalization of miniF2F test problem mathd_algebra_459: a rational linear
  system determines a value whose reduced numerator and denominator sum to 28. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory ratTheory;

val mathd_algebra_459 =
  ``!a b c d : rat.
      3 * a = b + c + d /\
      4 * b = a + c + d /\
      2 * c = a + b + d /\
      8 * a + 10 * b + 6 * c = 24
      ==>
      RATN d + &(RATD d) = 28``;
