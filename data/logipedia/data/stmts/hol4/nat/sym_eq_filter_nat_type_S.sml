(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_filter_nat_type_S (catalog title
  "nat.sym_eq_filter_nat_type_S"): for every result type, function on natural
  numbers, and natural number n, Leibniz equality relates the function's value
  at the successor of n to filter_nat_type applied at that successor. This file
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

val nat_sym_eq_filter_nat_type_S =
  ``!(return_ : num -> 'a) (n : num).
      logipedia_leibniz
        (return_ (SUC n))
        (logipedia_nat_filter_nat_type return_ (SUC n))``;
