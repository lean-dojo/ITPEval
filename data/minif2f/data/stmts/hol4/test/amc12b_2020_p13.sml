(*
  Statement-only formalization of miniF2F test problem amc12b_2020_p13: an identity relating
  square roots and ratios of natural logarithms of 2, 3, and 6. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory realTheory transcTheory;

val amc12b_2020_p13 =
  ``sqrt (ln (&6) / ln (&2) + ln (&6) / ln (&3)) =
    sqrt (ln (&3) / ln (&2)) + sqrt (ln (&2) / ln (&3))``;
