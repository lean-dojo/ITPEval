(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.let_clause_15311 (catalog title "primes.let_clause_15311"): for
  natural numbers n and m, if m is positive and n divides m, then for every
  natural d and p, m = n * (p + 1) implies m = n + n * p. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_let_clause_15311 =
  ``!(n : num) (m : num).
      0 < m ==>
      divides n m ==>
      !d : num.
        !p : num.
          m = n * SUC p ==>
          m = n + n * p``;
