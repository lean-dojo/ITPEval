(*
  Statement-only formalization of the Logipedia corpus artifact
  primes.divides_n_n (catalog title "primes.divides_n_n"): every natural
  number divides itself. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory dividesTheory;

val primes_divides_n_n =
  ``!n : num. divides n n``;
