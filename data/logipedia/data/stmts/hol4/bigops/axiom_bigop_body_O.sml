(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.axiom_bigop_body_O: at natural-number index zero,
  connectives.equal relates bigop_body to the function that returns the base
  element for every Boolean selector, binary operation, and natural-numbered
  family. This file contains no proof.
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
  "logipedia_bigops_bigop_body",
  logipedia_bigops_operator_type);

val bigops_axiom_bigop_body_O =
  ``logipedia_connectives_equal
      (logipedia_bigops_bigop_body 0)
      (\(p : num -> bool) (nil : 'a) (op : 'a -> 'a -> 'a)
        (f : num -> 'a). nil)``;
