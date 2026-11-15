(*
  Statement-only formalization of the Thousand Theorems corpus artifact
  Q1506253, "Euclid's theorem": for every natural-number threshold, there is
  a prime natural number at least as large. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val exists_infinite_primes =
  ``!n : num. ?p : num. n <= p /\ prime p``;
