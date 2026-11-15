(*
  Statement-only formalization of PutnamBench artifact putnam_1977_a5:
  for a prime p and natural numbers m >= n, the binomial coefficients
  binomial (p*m) (p*n) and binomial m n are congruent modulo p. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory;

val putnam_1977_a5 =
  ``!p m n : num.
      prime p /\ n <= m
      ==>
      binomial (p * m) (p * n) MOD p = binomial m n MOD p``;
