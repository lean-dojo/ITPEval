(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_times_body_O (catalog title "nat.axiom_times_body_O"): the
  module's abstract equality relation identifies times_body at
  natural-number zero with the constant-zero function. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_times_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_times_body",
  logipedia_nat_times_operator_type);

val nat_axiom_times_body_O =
  ``logipedia_connectives_equal
      (logipedia_nat_times_body 0)
      (\m. 0)``;
