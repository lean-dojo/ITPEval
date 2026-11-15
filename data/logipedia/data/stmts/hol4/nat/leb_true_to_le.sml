(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.leb_true_to_le (catalog title "nat.leb_true_to_le"): if the Boolean
  natural-number comparison leb returns true, then the first number is at
  most the second. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_nat_leb_def = Define `
  (logipedia_nat_leb 0 m = T) /\
  (logipedia_nat_leb (SUC n) 0 = F) /\
  (logipedia_nat_leb (SUC n) (SUC m) =
     logipedia_nat_leb n m)
`;

val nat_leb_true_to_le =
  ``!(n : num) (m : num).
      (logipedia_nat_leb n m = T) ==> n <= m``;
