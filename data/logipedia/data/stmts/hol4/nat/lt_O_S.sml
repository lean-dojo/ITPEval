(*
  Statement-only formalization of the Logipedia corpus artifact nat.lt_O_S
  (catalog title "nat.lt_O_S"): zero is strictly less than the successor of
  every natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_lt_O_S =
  ``!n : num. 0 < SUC n``;
