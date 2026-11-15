(*
  Statement-only formalization of miniF2F valid problem induction_sum_odd: for every natural
  number n, the sum of the first n odd natural numbers equals n squared. This file contains no
  proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory;

val induction_sum_odd =
  ``!n : num.
      SIGMA (\k. 2 * k + 1) (count n) = n EXP 2``;
