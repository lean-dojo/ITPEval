(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.not_eq_to_eqb_false (catalog title "nat.not_eq_to_eqb_false"):
  inequality of two natural numbers implies that their Boolean equality test
  returns false. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_eqb_def = new_definition (
  "logipedia_nat_eqb_def",
  ``logipedia_nat_eqb (n : num) (m : num) <=> n = m``);

val nat_not_eq_to_eqb_false =
  ``!(n : num) (m : num).
      ~(n = m) ==> (logipedia_nat_eqb n m = F)``;
