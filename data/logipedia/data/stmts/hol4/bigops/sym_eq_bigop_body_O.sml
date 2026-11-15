(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sym_eq_bigop_body_O: at natural-number index zero, Leibniz equality
  relates the function that returns the base element to bigop_body for every
  Boolean selector, binary operation, and natural-numbered family. This file
  contains no proof.
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
  "logipedia_bigops_bigop_body",
  logipedia_bigops_operator_type);

val bigops_sym_eq_bigop_body_O =
  ``logipedia_leibniz
      (\(p : num -> bool) (nil : 'a) (op : 'a -> 'a -> 'a)
        (f : num -> 'a). nil)
      (logipedia_bigops_bigop_body 0)``;
