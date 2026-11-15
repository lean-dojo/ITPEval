(*
  Statement-only formalization of miniF2F test problem amc12b_2020_p21: counting positive
  natural numbers whose shifted quotient equals the floor of their square root. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory
     transcTheory;

val amc12b_2020_p21 =
  ``FINITE
      {n : num |
         0 < n /\
         (&n + 1000) / 70 =
           real_of_int (INT_FLOOR (sqrt (&n)))} /\
    CARD
      {n : num |
         0 < n /\
         (&n + 1000) / 70 =
           real_of_int (INT_FLOOR (sqrt (&n)))} =
      6``;
