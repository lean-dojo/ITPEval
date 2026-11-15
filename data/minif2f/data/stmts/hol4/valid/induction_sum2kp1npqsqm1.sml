(*
  Statement-only formalization of miniF2F valid problem induction_sum2kp1npqsqm1: the finite
  sum of 2 * k + 3 over natural numbers k < n equals (n + 1)^2 - 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val induction_sum2kp1npqsqm1 =
  ``!n : num.
      SIGMA (\k. 2 * k + 3) (count n) =
        (n + 1) EXP 2 - 1``;
