(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2000_b2:
  for natural numbers n >= m >= 1, n divides the product of gcd(m,n) and
  the binomial coefficient n choose m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory combinatoricsTheory dividesTheory gcdTheory;

val putnam_2000_b2 =
  ``!m n : num.
      1 <= m
      ==>
      (m <= n
       ==>
       n divides (gcd m n * binomial n m))``;
