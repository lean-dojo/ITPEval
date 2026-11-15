(*
  Statement-only formalization of miniF2F artifact
  induction_divisibility_9div10tonm1: divisibility of 10^n - 1 by 9 for every
  positive natural number n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val induction_divisibility_9div10tonm1 =
  ``!n : num.
      0 < n ==>
      divides 9 (10 EXP n - 1)``;
