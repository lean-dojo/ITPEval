(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_Sn_O (catalog title "nat.not_le_Sn_O"): no successor of a
  natural number is less than or equal to zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_le_Sn_O =
  ``!n : num. ~(SUC n <= 0)``;
