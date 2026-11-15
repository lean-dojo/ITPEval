(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eqb_true_to_eq (catalog title "nat.eqb_true_to_eq"): if the Boolean
  equality test on two natural numbers returns true, then the numbers are
  equal. This file contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open arithmeticTheory;

val logipedia_nat_eqb_def = Define `
  (logipedia_nat_eqb 0 0 = T) /\
  (logipedia_nat_eqb 0 (SUC m) = F) /\
  (logipedia_nat_eqb (SUC n) 0 = F) /\
  (logipedia_nat_eqb (SUC n) (SUC m) =
     logipedia_nat_eqb n m)`;

val nat_eqb_true_to_eq =
  ``!(n : num) (m : num).
      (logipedia_nat_eqb n m = T) ==> n = m``;
