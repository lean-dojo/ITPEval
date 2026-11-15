(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.reflexive_divides (catalog title "primes.reflexive_divides"):
  natural-number divisibility is reflexive, so every natural number divides
  itself. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_reflexive_divides =
  ``!n : num. divides n n``;
