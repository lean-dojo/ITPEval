(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sym_eq_bigop_S: at every successor natural-number index, Leibniz
  equality relates the polymorphic higher-order operator bigop_body to bigop
  as functions of a Boolean selector, a base element, a binary operation, and
  a natural-numbered family. This file contains no proof.
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

val bigops_sym_eq_bigop_S =
  ``!n : num.
      logipedia_leibniz
        (logipedia_bigops_bigop_body (SUC n))
        (logipedia_bigops_bigop (SUC n))``;
