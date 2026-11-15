(*
  Statement-only formalization of miniF2F test problem
  algebra_amgm_sum1toneqn_prod1tonleq1: the finite AM-GM product bound for a
  nonnegative real sequence whose first n terms sum to n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory;

val algebra_amgm_sum1toneqn_prod1tonleq1 =
  ``!a : num -> real. !n : num.
      (!k. 0 <= a k) /\
      SIGMA a (count n) = &n
      ==>
      REAL_PROD_IMAGE a (count n) <= 1``;
