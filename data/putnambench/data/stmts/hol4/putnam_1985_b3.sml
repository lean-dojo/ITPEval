(*
  Statement-only formalization of PutnamBench corpus artifact putnam_1985_b3:
  a positive-integer array in which every positive integer occurs exactly
  eight times has an entry greater than the product of its positive indices.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pairTheory pred_setTheory;

val putnam_1985_b3 =
  ``!a : num -> num -> num.
      (!m n : num. 0 < a m n) /\
      (!k : num.
         0 < k
         ==>
         FINITE
           {p : num # num |
              0 < FST p /\
              0 < SND p /\
              a (FST p) (SND p) = k} /\
         CARD
           {p : num # num |
              0 < FST p /\
              0 < SND p /\
              a (FST p) (SND p) = k} = 8)
      ==>
      ?m n : num.
        0 < m /\ 0 < n /\ m * n < a m n``;
