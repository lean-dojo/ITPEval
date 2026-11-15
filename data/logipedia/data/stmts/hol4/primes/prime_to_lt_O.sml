(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.prime_to_lt_O (catalog title "primes.prime_to_lt_O"): every prime
  natural number is strictly positive. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_prime_to_lt_O =
  ``!p : num. prime p ==> 0 < p``;
