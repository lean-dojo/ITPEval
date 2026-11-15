(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.eq_mod_to_divides (catalog title "primes.eq_mod_to_divides"): for
  natural numbers n, m, and positive q, equal remainders modulo q imply that
  q divides the truncated natural-number difference n - m. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_eq_mod_to_divides =
  ``!n m q : num.
      0 < q ==>
      n MOD q = m MOD q ==>
      divides q (n - m)``;
