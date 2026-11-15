(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_leb_body_O (catalog title "nat.axiom_leb_body_O"): at
  natural-number index zero, connectives.equal relates leb_body to the
  constant-true function on natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_leb_body_type =
  numSyntax.num -->
  numSyntax.num -->
  Type.bool;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_leb_body",
  logipedia_nat_leb_body_type);

val nat_axiom_leb_body_O =
  ``logipedia_connectives_equal
      (logipedia_nat_leb_body 0)
      (\(m : num). T)``;
