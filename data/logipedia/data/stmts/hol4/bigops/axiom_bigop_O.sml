(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.axiom_bigop_O: at natural-number index zero, connectives.equal
  relates the polymorphic higher-order operators bigop and bigop_body as
  functions of a Boolean selector, a base element, a binary operation, and a
  natural-numbered family. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_bigops_operator_type =
  numSyntax.num -->
  (numSyntax.num --> Type.bool) -->
  Type.alpha -->
  (Type.alpha --> Type.alpha --> Type.alpha) -->
  (numSyntax.num --> Type.alpha) -->
  Type.alpha;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_bigops_bigop",
  logipedia_bigops_operator_type);

val _ = new_constant (
  "logipedia_bigops_bigop_body",
  logipedia_bigops_operator_type);

val bigops_axiom_bigop_O =
  ``logipedia_connectives_equal
      (logipedia_bigops_bigop 0)
      (logipedia_bigops_bigop_body 0)``;
