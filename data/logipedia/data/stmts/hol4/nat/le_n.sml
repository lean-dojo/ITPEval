(*
  Statement-only formalization of the Logipedia corpus artifact nat.le_n
  (catalog title "nat.le_n"): every natural number is less than or equal to
  itself. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_n =
  ``!n : num. n <= n``;
