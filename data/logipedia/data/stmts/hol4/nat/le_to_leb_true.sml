(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.le_to_leb_true (catalog title "nat.le_to_leb_true"): natural-number
  less-than-or-equal implies that the corresponding Boolean comparison is
  true. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_nat_leb_def = Define `
  (logipedia_nat_leb 0 m = T) /\
  (logipedia_nat_leb (SUC n) 0 = F) /\
  (logipedia_nat_leb (SUC n) (SUC m) =
     logipedia_nat_leb n m)`;

val nat_le_to_leb_true =
  ``!(n : num) (m : num).
      n <= m ==> (logipedia_nat_leb n m = T)``;
