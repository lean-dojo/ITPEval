(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.dividesb_false_to_not_divides (catalog title
  "primes.dividesb_false_to_not_divides"): for natural numbers n and m, if
  the Boolean divisibility test for n dividing m returns false, then n does
  not divide m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_primes_dividesb_def = new_definition (
  "logipedia_primes_dividesb_def",
  ``logipedia_primes_dividesb (n : num) (m : num) <=> m MOD n = 0``);

val primes_dividesb_false_to_not_divides =
  ``!(n : num) (m : num).
      logipedia_primes_dividesb n m = F ==>
      ~divides n m``;
