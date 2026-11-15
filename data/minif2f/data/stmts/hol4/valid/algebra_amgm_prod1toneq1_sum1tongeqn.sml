(*
  Statement-only formalization of miniF2F valid problem
  algebra_amgm_prod1toneq1_sum1tongeqn: the AM-GM bound that n nonnegative
  real terms with product one have sum at least n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val algebra_amgm_prod1toneq1_sum1tongeqn =
  ``!a : num -> real. !n : num.
      (!k. 0 <= a k) /\
      REAL_PROD_IMAGE a (count n) = 1
      ==>
      &n <= SIGMA a (count n)``;
