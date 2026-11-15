(*
  Statement-only formalization of miniF2F valid problem induction_sum_1oktkp1:
  the finite telescoping sum of reciprocal products of consecutive positive
  integers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val induction_sum_1oktkp1 =
  ``!n : num.
      SIGMA
        (\k : num.
          (1 : real) / ((&(k + 1) : real) * &(k + 2)))
        (count n) =
      (&n : real) / &(n + 1)``;
