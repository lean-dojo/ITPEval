(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_n_O_to_eq (catalog title "nat.le_n_O_to_eq"): every natural number
  less than or equal to zero is equal to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_n_O_to_eq =
  ``!n : num. n <= 0 ==> 0 = n``;
