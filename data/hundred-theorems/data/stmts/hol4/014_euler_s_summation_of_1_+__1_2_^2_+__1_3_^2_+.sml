(*
  Statement-only formalization of "Euler's Summation of 1 + (1/2)^2 + (1/3)^2 + ..." from Hundred
  Theorems item 014. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory pred_setTheory realTheory real_sigmaTheory transcTheory;
open real_topologyTheory;

val euler_summation_of_inverse_squares =
  ``((\k : num.
       SIGMA
         (\n : num. (1 : real) / ((&(n + 1) : real) pow 2))
         (count k)) --> (pi pow 2 / 6 : real)) sequentially``;
