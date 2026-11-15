(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a1:
  the number of positive integers divisible by 2020, having at most 2020
  decimal digits, and consisting of consecutive ones followed by consecutive
  zeros is 508536. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val putnam_2020_a1 =
  ``CARD
      {n : num |
         divides 2020 n /\
         n < 10 EXP 2020 /\
         ?k l : num.
           l <= k /\
           n =
             SIGMA
               (\i : num. 10 EXP (i + l))
               (count (k - l + 1))} =
    508536``;
