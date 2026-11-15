(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_minus_body_O (catalog title "nat.axiom_minus_body_O"): at
  natural-number index zero, connectives.equal relates minus_body to the
  constant-zero function on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_minus_body_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_minus_body",
  logipedia_nat_minus_body_type);

val nat_axiom_minus_body_O =
  ``logipedia_connectives_equal
      (logipedia_nat_minus_body 0)
      (\(m : num). 0)``;
