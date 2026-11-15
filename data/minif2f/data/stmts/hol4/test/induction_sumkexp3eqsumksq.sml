(*
  Statement-only formalization of miniF2F test problem induction_sumkexp3eqsumksq: for every
  natural number n, the sum of the cubes of the naturals below n equals the square of their
  sum. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val induction_sumkexp3eqsumksq =
  ``!n : num.
      SIGMA (\k : num. k EXP 3) (count n) =
      (SIGMA (\k : num. k) (count n)) EXP 2``;
