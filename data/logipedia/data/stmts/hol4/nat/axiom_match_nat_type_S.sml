(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_match_nat_type_S (catalog title
  "nat.axiom_match_nat_type_S"): for every result type, zero branch,
  successor branch, and natural number n, connectives.equal relates the
  polymorphic natural-number matcher at the successor of n to the successor
  branch applied to n. This file contains no proof.
*)

open HolKernel Parse boolLib;
open arithmeticTheory;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val _ = new_constant (
  "logipedia_nat_match_nat_type",
  Type.alpha -->
  (numSyntax.num --> Type.alpha) -->
  numSyntax.num -->
  Type.alpha);

val nat_axiom_match_nat_type_S =
  ``!(case_O : 'a) (case_S : num -> 'a) (n : num).
      logipedia_connectives_equal
        (logipedia_nat_match_nat_type case_O case_S (SUC n))
        (case_S n)``;
