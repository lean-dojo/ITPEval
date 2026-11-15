(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_Sn_n (catalog title "nat.not_le_Sn_n"): no natural number's
  successor is less than or equal to that number. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_le_Sn_n =
  ``!n : num. ~(SUC n <= n)``;
