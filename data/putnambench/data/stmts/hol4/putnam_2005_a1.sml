(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2005_a1:
  every positive integer is a nonempty finite sum of terms 2^r * 3^s with
  nonnegative exponents, no one of which divides another. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory pred_setTheory;

val putnam_2005_a1 =
  ``!n : num.
      0 < n
      ==>
      ?k : num. ?a : num -> num # num.
        0 < k /\
        n =
          SIGMA
            (\i : num.
               2 EXP (FST (a i)) * 3 EXP (SND (a i)))
            (count k) /\
        !i j : num.
          i IN count k /\ j IN count k /\ i <> j
          ==>
          ~divides
             (2 EXP (FST (a i)) * 3 EXP (SND (a i)))
             (2 EXP (FST (a j)) * 3 EXP (SND (a j)))``;
