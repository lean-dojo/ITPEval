(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1995_b6:
  three positive-real Beatty sets cannot be pairwise disjoint and together
  cover all positive natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory realTheory intrealTheory;

val putnam_1995_b6 =
  ``let S =
      \alpha : real.
        {x : num |
           ?n : num.
             1 <= n /\
             int_of_num x = INT_FLOOR ((&n : real) * alpha)}
    in
      ~(?alpha beta gamma : real.
          0 < alpha /\
          0 < beta /\
          0 < gamma /\
          DISJOINT (S alpha) (S beta) /\
          DISJOINT (S beta) (S gamma) /\
          DISJOINT (S alpha) (S gamma) /\
          {x : num | 1 <= x} =
            (S alpha) UNION (S beta) UNION (S gamma))``;
