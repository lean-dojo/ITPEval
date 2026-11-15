(*
  Statement-only formalization of the Logipedia corpus artifact
  bigops.sym_eq_bigop_body_S: at every successor natural-number index,
  Leibniz equality relates the Boolean-selected clause that combines the
  current family value with the preceding bigop result to bigop_body. This
  file contains no proof.
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

val bigops_sym_eq_bigop_body_S =
  ``!n : num.
      logipedia_leibniz
        (\(p : num -> bool) (nil : 'a) (op : 'a -> 'a -> 'a)
          (f : num -> 'a).
            if p n then
              op (f n) (logipedia_bigops_bigop n p nil op f)
            else
              logipedia_bigops_bigop n p nil op f)
        (logipedia_bigops_bigop_body (SUC n))``;
