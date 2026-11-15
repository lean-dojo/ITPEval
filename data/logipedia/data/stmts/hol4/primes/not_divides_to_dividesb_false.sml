(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.not_divides_to_dividesb_false (catalog title
  "primes.not_divides_to_dividesb_false"): for natural numbers n and m, if n
  is positive and does not divide m, then the Boolean divisibility test
  returns false. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val logipedia_primes_dividesb_def = new_definition (
  "logipedia_primes_dividesb_def",
  ``logipedia_primes_dividesb (n : num) (m : num) <=> m MOD n = 0``);

val primes_not_divides_to_dividesb_false =
  ``!(n : num) (m : num).
      0 < n ==>
      ~divides n m ==>
      logipedia_primes_dividesb n m = F``;
