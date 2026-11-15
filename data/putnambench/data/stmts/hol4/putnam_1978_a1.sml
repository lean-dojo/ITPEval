(*
  Statement-only formalization of PutnamBench artifact putnam_1978_a1:
  every 20-element subset of the integer progression 1, 4, 7, ..., 100
  contains two distinct elements whose sum is 104. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory integerTheory pred_setTheory;

val putnam_1978_a1 =
  ``!S T : int set.
      S =
        {k : int |
           ?j : int.
             0 <= j /\ j <= 33 /\ k = 3 * j + 1} /\
      T SUBSET S /\
      CARD T = 20
      ==>
      ?m n : int.
        m IN T /\ n IN T /\ m <> n /\ m + n = 104``;
