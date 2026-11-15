(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_to_eqb_true (catalog title "nat.eq_to_eqb_true"): equality of two
  natural numbers implies that their Boolean equality test returns true.
  This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_eqb_def = new_definition (
  "logipedia_nat_eqb_def",
  ``logipedia_nat_eqb (n : num) (m : num) <=> n = m``);

val nat_eq_to_eqb_true =
  ``!(n : num) (m : num).
      n = m ==> (logipedia_nat_eqb n m = T)``;
