(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_plus_body_O (catalog title "nat.eq_plus_body_O"): Leibniz equality
  identifies plus_body at natural-number zero with the identity function on
  natural numbers. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_nat_plus_body_type =
  numSyntax.num -->
  numSyntax.num -->
  numSyntax.num;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_plus_body",
  logipedia_nat_plus_body_type);

val nat_eq_plus_body_O =
  ``logipedia_leibniz
      (logipedia_nat_plus_body 0)
      (\m : num. m)``;
