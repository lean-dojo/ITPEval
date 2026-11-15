(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.decidable_divides (catalog title "primes.decidable_divides"):
  divisibility is decidable for every pair of natural numbers. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_decidable_divides =
  ``!(n : num) (m : num). divides n m \/ ~divides n m``;
