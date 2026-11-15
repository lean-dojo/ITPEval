(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_times_body_O (catalog title "nat.sym_eq_times_body_O"):
  Leibniz equality relates the constant-zero function on natural numbers to
  times_body at natural-number zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_times_body_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_times_body",
  logipedia_nat_times_body_type);

val nat_sym_eq_times_body_O =
  ``logipedia_leibniz
      (\m : num. 0)
      (logipedia_nat_times_body 0)``;
