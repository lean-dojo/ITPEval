(*
  Statement-only formalization of miniF2F valid problem
  induction_divisibility_3divnto3m2n: divisibility of n^3 + 2*n by 3 for every
  natural number n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val induction_divisibility_3divnto3m2n =
  ``!n : num.
      divides 3 (n EXP 3 + 2 * n)``;
