(*
  Statement-only formalization of the Logipedia corpus artifact
  fact.eq_fact_body_O (catalog title "fact.eq_fact_body_O"): Leibniz equality
  identifies fact_body at natural-number zero with the successor of zero.
  This file contains no proof.
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

val fact_eq_fact_body_O =
  ``logipedia_leibniz
      (logipedia_fact_fact_body 0)
      (SUC 0)``;
