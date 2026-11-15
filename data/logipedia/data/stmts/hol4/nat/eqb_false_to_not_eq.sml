(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eqb_false_to_not_eq (catalog title "nat.eqb_false_to_not_eq"): a false
  result from the Boolean equality test on two natural numbers implies that
  the numbers are unequal. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_eqb_def = new_definition (
  "logipedia_nat_eqb_def",
  ``logipedia_nat_eqb (n : num) (m : num) <=> n = m``);

val nat_eqb_false_to_not_eq =
  ``!(n : num) (m : num).
      (logipedia_nat_eqb n m = F) ==> ~(n = m)``;
