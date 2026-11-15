(*
  Statement-only formalization of the Logipedia corpus artifact
  exp.eq_exp_body_S (catalog title "exp.eq_exp_body_S"): for all natural
  numbers n and m, Leibniz equality relates exp_body n at the successor of m
  to exp n m multiplied by n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_exp_operator_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_exp_exp",
  logipedia_exp_operator_type);

val _ = new_constant (
  "logipedia_exp_exp_body",
  logipedia_exp_operator_type);

val exp_eq_exp_body_S =
  ``!n m : num.
      logipedia_leibniz
        (logipedia_exp_exp_body n (SUC m))
        (logipedia_exp_exp n m * n)``;
