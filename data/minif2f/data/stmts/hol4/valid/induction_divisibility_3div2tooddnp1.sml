(*
  Statement-only formalization of miniF2F valid problem
  induction_divisibility_3div2tooddnp1: divisibility of 2^(2*n+1) + 1 by 3
  for every natural number n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val induction_divisibility_3div2tooddnp1 =
  ``!n : num. divides 3 (2 EXP (2 * n + 1) + 1)``;
