(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_plus_body_S (catalog title "nat.eq_plus_body_S"): for every natural
  number n, Leibniz equality identifies plus_body at the successor of n with
  the function mapping m to the successor of plus n m. This file contains no
  proof.
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

val nat_eq_plus_body_S =
  ``!n : num.
      logipedia_leibniz
        (logipedia_nat_plus_body (SUC n))
        (\m : num. SUC (logipedia_nat_plus n m))``;
