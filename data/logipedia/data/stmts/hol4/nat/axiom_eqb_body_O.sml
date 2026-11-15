(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_eqb_body_O (catalog title "nat.axiom_eqb_body_O"): the source
  equality predicate relates eqb_body at natural-number zero to the Boolean
  function that is true at zero and false at every successor. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_eqb_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  Type.bool;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_eqb_body",
  logipedia_nat_eqb_operator_type);

val nat_axiom_eqb_body_O =
  ``logipedia_connectives_equal
      (logipedia_nat_eqb_body 0)
      (\m : num. m = 0)``;
