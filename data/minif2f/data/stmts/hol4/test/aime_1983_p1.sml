(*
  Statement-only formalization of miniF2F test problem aime_1983_p1: natural-number
  logarithm-base relations determining that the logarithm of w to base z is 60.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val aime_1983_p1 =
  ``!x y z w : num.
      ((1 < x) /\ (1 < y) /\ (1 < z)) /\
      (0 <= w) /\
      (ln (&w) / ln (&x) = 24) /\
      (ln (&w) / ln (&y) = 40) /\
      (ln (&w) / ln (&(x * y * z)) = 12)
      ==>
      (ln (&w) / ln (&z) = 60)``;
