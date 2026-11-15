(*
  Statement-only formalization of the Logipedia corpus artifact nat.minus_n_n
  (catalog title "nat.minus_n_n"): subtracting any natural number from itself
  yields zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_minus_n_n =
  ``!n : num. 0 = n - n``;
