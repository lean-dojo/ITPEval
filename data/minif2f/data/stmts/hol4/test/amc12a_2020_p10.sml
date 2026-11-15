(*
  Statement-only formalization of miniF2F test problem amc12a_2020_p10: a nested logarithmic
  equation implies that the natural number's decimal digit sum is 13. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory listTheory numposrepTheory realTheory transcTheory;

val amc12a_2020_p10 =
  ``!n : num.
      1 < n /\
      (ln (ln (&n) / ln (&16)) / ln (&2) =
       ln (ln (&n) / ln (&4)) / ln (&4))
      ==>
      SUM (num_to_dec_list n) = 13``;
