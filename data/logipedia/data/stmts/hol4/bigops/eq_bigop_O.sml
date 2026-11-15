(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.eq_bigop_O: at natural-number index zero, Leibniz equality relates
  the polymorphic higher-order operators bigop and bigop_body as functions of
  a Boolean selector, a base element, a binary operation, and a
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

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_bigops_bigop",
  logipedia_bigops_operator_type);

val _ = new_constant (
  "logipedia_bigops_bigop_body",
  logipedia_bigops_operator_type);

val bigops_eq_bigop_O =
  ``logipedia_leibniz
      (logipedia_bigops_bigop 0)
      (logipedia_bigops_bigop_body 0)``;
