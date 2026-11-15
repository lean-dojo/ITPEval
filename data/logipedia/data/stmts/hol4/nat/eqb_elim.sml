(*
  Statement-only formalization of the Logipedia corpus artifact nat.eqb_elim
  (catalog title "nat.eqb_elim"): for arbitrary natural numbers and a
  Boolean predicate, the equality and disequality branches establish the
  predicate at true and false, respectively, and hence at the Boolean
  equality test. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_eqb_def = new_definition (
  "logipedia_nat_eqb_def",
  ``logipedia_nat_eqb (n : num) (m : num) <=> n = m``);

val nat_eqb_elim =
  ``!(n : num) (m : num) (P : bool -> bool).
      (n = m ==> P T) ==>
      (~(n = m) ==> P F) ==>
      P (logipedia_nat_eqb n m)``;
