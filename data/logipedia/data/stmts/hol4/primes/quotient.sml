(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.quotient (catalog title "primes.quotient"): for natural numbers
  n, m, and q, if m equals n times q, then n divides m. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_quotient =
  ``!(n : num) (m : num) (q : num).
      m = n * q ==>
      divides n m``;
