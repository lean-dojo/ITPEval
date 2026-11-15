(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_times_body_O (catalog title "nat.eq_times_body_O"): Leibniz equality
  identifies times_body at natural-number zero with the constant-zero
  function on natural numbers. This file contains no proof.
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

val nat_eq_times_body_O =
  ``logipedia_leibniz
      (logipedia_nat_times_body 0)
      (\m : num. 0)``;
