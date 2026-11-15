(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.dividesb_true_to_divides (catalog title
  "primes.dividesb_true_to_divides"): for natural numbers n and m, if the
  Boolean divisibility test for n dividing m returns true, then n divides m.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_primes_dividesb_def = new_definition (
  "logipedia_primes_dividesb_def",
  ``logipedia_primes_dividesb (n : num) (m : num) <=> m MOD n = 0``);

val primes_dividesb_true_to_divides =
  ``!(n : num) (m : num).
      logipedia_primes_dividesb n m = T ==>
      divides n m``;
