(*
  Statement-only formalization of the Logipedia corpus artifact
  fact.sym_eq_fact_body_O (catalog title "fact.sym_eq_fact_body_O"):
  Leibniz equality identifies the successor of natural-number zero with
  fact_body at zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_fact_fact_body",
  numSyntax.num --> numSyntax.num);

val fact_sym_eq_fact_body_O =
  ``logipedia_leibniz
      (SUC 0)
      (logipedia_fact_fact_body 0)``;
