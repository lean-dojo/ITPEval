(*
  Statement-only formalization of miniF2F valid problem aime_1988_p3: a nested logarithm
  equation on x > 1 determining the square of the base-2 logarithm. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open realTheory transcTheory;

val aime_1988_p3 =
  ``!x : real.
      1 < x /\
      (ln (ln x / ln 8) / ln 2 =
       ln (ln x / ln 2) / ln 8)
      ==>
      (ln x / ln 2) pow 2 = 27``;
