(*
  Statement-only formalization of "The Infinitude of Primes" from Hundred Theorems item 011.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val infinitude_of_primes =
  ``!n : num. ?p : num. prime p /\ n < p``;
