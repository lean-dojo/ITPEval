(*
  Statement-only formalization of the Logipedia corpus artifact nat.minus_n_O
  (catalog title "nat.minus_n_O"): subtracting zero from any natural number
  yields that natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_n_O =
  ``!n : num. n = n - 0``;
