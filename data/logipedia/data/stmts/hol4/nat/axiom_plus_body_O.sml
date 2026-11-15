(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_plus_body_O (catalog title "nat.axiom_plus_body_O"): the source
  equality predicate relates plus_body at natural-number zero to the identity
  function on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_plus_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_plus_body",
  logipedia_nat_plus_operator_type);

val nat_axiom_plus_body_O =
  ``logipedia_connectives_equal
      (logipedia_nat_plus_body 0)
      (\m : num. m)``;
