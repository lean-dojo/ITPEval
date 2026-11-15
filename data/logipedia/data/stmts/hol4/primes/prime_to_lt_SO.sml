(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.prime_to_lt_SO (catalog title "primes.prime_to_lt_SO"): every prime
  natural number is strictly greater than one. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_prime_to_lt_SO =
  ``!p : num. prime p ==> 1 < p``;
