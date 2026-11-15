(*
  Statement-only formalization of the Logipedia corpus artifact fact.eq_fact
  (catalog title "fact.eq_fact"): for every natural number n, Leibniz equality
  relates fact n to filter_nat_type applied to fact_body at n. This file
  contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_filter_nat_type_type =
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_filter_nat_type",
  logipedia_nat_filter_nat_type_type);

val _ = new_constant (
  "logipedia_fact_fact",
  numSyntax.num --> numSyntax.num);

val _ = new_constant (
  "logipedia_fact_fact_body",
  numSyntax.num --> numSyntax.num);

val fact_eq_fact =
  ``!n : num.
      logipedia_leibniz
        (logipedia_fact_fact n)
        (logipedia_nat_filter_nat_type
           logipedia_fact_fact_body n)``;
