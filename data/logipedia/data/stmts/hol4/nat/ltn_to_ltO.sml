(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.ltn_to_ltO (catalog title "nat.ltn_to_ltO"): for natural numbers n
  and m, n < m implies 0 < m. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_ltn_to_ltO =
  ``!n m : num. n < m ==> 0 < m``;
