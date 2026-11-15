(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_plus_body_S (catalog title "nat.sym_eq_plus_body_S"): for every
  natural number n, Leibniz equality relates the function mapping m to the
  successor of plus n m to plus_body at the successor of n. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_plus_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_plus",
  logipedia_nat_plus_operator_type);

val _ = new_constant (
  "logipedia_nat_plus_body",
  logipedia_nat_plus_operator_type);

val nat_sym_eq_plus_body_S =
  ``!n : num.
      logipedia_leibniz
        (\m : num. SUC (logipedia_nat_plus n m))
        (logipedia_nat_plus_body (SUC n))``;
