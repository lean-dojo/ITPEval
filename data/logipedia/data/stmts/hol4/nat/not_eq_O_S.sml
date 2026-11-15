(*
  Statement-only formalization of the Logipedia corpus artifact nat.not_eq_O_S
  (catalog title "nat.not_eq_O_S"): zero is not equal to the successor of any
  natural number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_eq_O_S =
  ``!n : num. ~(0 = SUC n)``;
