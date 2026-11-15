(*
  Statement-only formalization of miniF2F valid problem numbertheory_sumkmulnckeqnmul2pownm1.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory;

val numbertheory_sumkmulnckeqnmul2pownm1 =
  ``!n : num.
      0 < n
      ==>
      SIGMA
        (\k. k * binomial n k)
        (IMAGE SUC (count n)) =
      n * 2 EXP (n - 1)``;
