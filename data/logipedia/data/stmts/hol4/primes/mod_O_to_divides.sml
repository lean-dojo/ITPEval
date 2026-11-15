(*
  Statement-only formalization of Logipedia corpus artifact
  primes.mod_O_to_divides (catalog title "primes.mod_O_to_divides"): for
  natural numbers n and m, if n is positive and m has remainder zero modulo
  n, then n divides m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_mod_O_to_divides =
  ``!n m : num.
      0 < n ==>
      m MOD n = 0 ==>
      divides n m``;
