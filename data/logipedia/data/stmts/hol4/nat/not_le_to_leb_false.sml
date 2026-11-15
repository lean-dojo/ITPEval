(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_le_to_leb_false (catalog title "nat.not_le_to_leb_false"):
  failure of natural-number less-than-or-equal implies that the corresponding
  Boolean comparison returns false. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_leb_def = new_definition (
  "logipedia_nat_leb_def",
  ``logipedia_nat_leb (n : num) (m : num) <=> n <= m``);

val nat_not_le_to_leb_false =
  ``!(n : num) (m : num).
      ~(n <= m) ==> (logipedia_nat_leb n m = F)``;
