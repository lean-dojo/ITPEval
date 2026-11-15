(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_times_body_S (catalog title "nat.sym_eq_times_body_S"): for every
  natural number n, Leibniz equality identifies the function mapping m to
  plus m (times n m) with times_body at the successor of n. This file contains
  no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_binary_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_plus",
  logipedia_nat_binary_operator_type);

val _ = new_constant (
  "logipedia_nat_times",
  logipedia_nat_binary_operator_type);

val _ = new_constant (
  "logipedia_nat_times_body",
  logipedia_nat_binary_operator_type);

val nat_sym_eq_times_body_S =
  ``!n : num.
      logipedia_leibniz
        (\m : num.
          logipedia_nat_plus m (logipedia_nat_times n m))
        (logipedia_nat_times_body (SUC n))``;
