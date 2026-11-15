(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2024_a1:
  the positive natural exponents admitting positive natural numbers a, b, and
  c with 2*a^n + 3*b^n = 4*c^n are exactly n = 1. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val putnam_2024_a1 =
  ``!n : num.
      (0 < n /\
       ?a b c : num.
         0 < a /\
         0 < b /\
         0 < c /\
         2 * a EXP n + 3 * b EXP n = 4 * c EXP n)
      <=>
      n = 1``;
