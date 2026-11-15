(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_n_O (catalog title "primes.divides_n_O"): every natural
  number divides zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_divides_n_O =
  ``!n : num. divides n 0``;
