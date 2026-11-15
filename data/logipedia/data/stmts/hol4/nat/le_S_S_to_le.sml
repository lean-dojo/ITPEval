(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_S_S_to_le (catalog title "nat.le_S_S_to_le"): successor
  cancellation for the natural-number less-than-or-equal relation. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_S_S_to_le =
  ``!(n : num) (m : num).
      SUC n <= SUC m ==> n <= m``;
