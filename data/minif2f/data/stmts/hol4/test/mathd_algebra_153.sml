(*
  Statement-only formalization of miniF2F test problem mathd_algebra_153: for the real number
  n = 1/3, the sum of the integer floors of 10n, 100n, 1000n, and 10000n is 3702. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open integerTheory realTheory intrealTheory;

val mathd_algebra_153 =
  ``!n : real.
      n = 1 / 3
      ==>
      INT_FLOOR (10 * n) + INT_FLOOR (100 * n) +
        INT_FLOOR (1000 * n) + INT_FLOOR (10000 * n) = 3702``;
