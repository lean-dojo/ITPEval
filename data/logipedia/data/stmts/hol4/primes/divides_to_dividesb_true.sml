(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_to_dividesb_true (catalog title
  "primes.divides_to_dividesb_true"): for natural numbers n and m, if n is
  positive and divides m, then the Boolean divisibility test returns true.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_primes_dividesb_def = new_definition (
  "logipedia_primes_dividesb_def",
  ``logipedia_primes_dividesb (n : num) (m : num) <=> m MOD n = 0``);

val primes_divides_to_dividesb_true =
  ``!(n : num) (m : num).
      0 < n ==>
      divides n m ==>
      logipedia_primes_dividesb n m = T``;
