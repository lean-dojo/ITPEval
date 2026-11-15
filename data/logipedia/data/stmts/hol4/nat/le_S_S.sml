(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_S_S (catalog title "nat.le_S_S"): successor preserves the
  natural-number less-than-or-equal relation. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val nat_le_S_S =
  ``!(n : num) (m : num).
      n <= m ==> SUC n <= SUC m``;
