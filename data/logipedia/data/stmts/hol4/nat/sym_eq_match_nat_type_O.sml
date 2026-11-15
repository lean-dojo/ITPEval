(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.sym_eq_match_nat_type_O (catalog title
  "nat.sym_eq_match_nat_type_O"): for every result type, zero branch, and
  successor branch, Leibniz equality relates the zero branch to the
  polymorphic natural-number matcher at zero. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val logipedia_leibniz_def = new_definition (
  "logipedia_leibniz_def",
  ``logipedia_leibniz (x : 'a) (y : 'a) <=>
      !P : 'a -> bool. P x ==> P y``);

val _ = new_constant (
  "logipedia_nat_match_nat_type",
  Type.alpha -->
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha);

val nat_sym_eq_match_nat_type_O =
  ``!(case_O : 'a) (case_S : num -> 'a).
      logipedia_leibniz
        case_O
        (logipedia_nat_match_nat_type case_O case_S 0)``;
