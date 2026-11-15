(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_filter_nat_type_O (catalog title
  "nat.sym_eq_filter_nat_type_O"): for every result type and function on
  natural numbers, Leibniz equality relates the function's value at zero to
  filter_nat_type applied at zero. This file contains no proof.
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

val nat_sym_eq_filter_nat_type_O =
  ``!return_ : num -> 'a.
      logipedia_leibniz
        (return_ 0)
        (logipedia_nat_filter_nat_type return_ 0)``;
