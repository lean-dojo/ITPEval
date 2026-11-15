(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.axiom_bigop_body_S: at every successor natural-number index,
  connectives.equal relates bigop_body to the Boolean-selected clause built
  from bigop, a base element, a binary operation, and a natural-numbered
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
  "logipedia_bool_match_bool_type",
  Type.alpha --> Type.alpha --> Type.bool --> Type.alpha);

val _ = new_constant (
  "logipedia_bigops_bigop",
  logipedia_bigops_operator_type);

val _ = new_constant (
  "logipedia_bigops_bigop_body",
  logipedia_bigops_operator_type);

val bigops_axiom_bigop_body_S =
  ``!n : num.
      logipedia_connectives_equal
        (logipedia_bigops_bigop_body (SUC n))
        (\(p : num -> bool) (nil : 'a) (op : 'a -> 'a -> 'a)
          (f : num -> 'a).
            logipedia_bool_match_bool_type
              (op (f n) (logipedia_bigops_bigop n p nil op f))
              (logipedia_bigops_bigop n p nil op f)
              (p n))``;
