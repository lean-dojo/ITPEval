(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_to_lt (catalog title "nat.not_le_to_lt"): for natural numbers,
  failure of non-strict order implies the reverse strict order. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_not_le_to_lt =
  ``!(n : num) (m : num).
      ~(n <= m) ==> m < n``;
