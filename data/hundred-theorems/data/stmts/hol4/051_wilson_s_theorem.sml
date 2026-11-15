(*
  Statement-only formalization of "Wilson's Theorem" from Hundred Theorems item 051.
  For every natural number n other than 1, n is prime if and only if (n - 1)!
  is congruent to -1 modulo n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val wilsons_theorem =
  ``!n : num.
      ~(n = 1) ==>
      (prime n <=>
       (FACT (n - 1)) MOD n = (n - 1) MOD n)``;
