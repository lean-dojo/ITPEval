(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2020_a2:
  the finite binomial sum from j = 0 through k of
  2^(k-j) times binomial (k+j) j equals 4^k. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory pred_setTheory;

val putnam_2020_a2 =
  ``!k : num.
      SIGMA
        (\j : num. 2 EXP (k - j) * binomial (k + j) j)
        (count (SUC k)) =
      4 EXP k``;
