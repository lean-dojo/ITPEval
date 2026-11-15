(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_mod_O (catalog title "primes.divides_to_mod_O"): for
  natural numbers n and m, if n is positive and divides m, then the remainder
  of m upon division by n is zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_divides_to_mod_O =
  ``!(n : num) (m : num).
      0 < n ==>
      divides n m ==>
      m MOD n = 0``;
