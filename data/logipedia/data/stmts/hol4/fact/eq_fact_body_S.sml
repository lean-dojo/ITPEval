(*
  Statement-only formalization of the Logipedia corpus artifact
  fact.eq_fact_body_S (catalog title "fact.eq_fact_body_S"): for every natural
  number n, Leibniz equality identifies fact_body at the successor of n with
  fact n multiplied by that successor. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_fact_fact",
  numSyntax.num --> numSyntax.num);

val _ = new_constant (
  "logipedia_fact_fact_body",
  numSyntax.num --> numSyntax.num);

val fact_eq_fact_body_S =
  ``!n : num.
      logipedia_leibniz
        (logipedia_fact_fact_body (SUC n))
        (logipedia_fact_fact n * SUC n)``;
