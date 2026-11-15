(*
  Statement-only formalization of "All Primes (1 mod 4) Equal the Sum of Two Squares" from
  Hundred Theorems item 020. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val all_primes_1_mod_4_equal_the_sum_of_two_squares =
  ``!p : num.
      prime p /\ p MOD 4 = 1 ==>
      ?x y : num. p = x EXP 2 + y EXP 2``;
