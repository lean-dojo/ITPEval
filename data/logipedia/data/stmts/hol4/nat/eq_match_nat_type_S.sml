(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.eq_match_nat_type_S (catalog title "nat.eq_match_nat_type_S"): for
  every result type, zero branch, successor branch, and natural number n,
  Leibniz equality relates the polymorphic natural-number matcher at the
  successor of n to the successor branch applied to n. This file contains no
  proof.
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

val nat_eq_match_nat_type_S =
  ``!(case_O : 'a) (case_S : num -> 'a) (n : num).
      logipedia_leibniz
        (logipedia_nat_match_nat_type case_O case_S (SUC n))
        (case_S n)``;
