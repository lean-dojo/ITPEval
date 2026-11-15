(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_O_n (catalog title "nat.le_O_n"): every natural number is greater
  than or equal to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_O_n =
  ``!n : num. 0 <= n``;
