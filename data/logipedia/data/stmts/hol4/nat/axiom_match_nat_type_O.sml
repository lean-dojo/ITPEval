(*
  Statement-only formalization of the Logipedia corpus artifact
  nat.axiom_match_nat_type_O (catalog title
  "nat.axiom_match_nat_type_O"): for every result type, zero branch, and
  successor branch, connectives.equal relates the polymorphic natural-number
  matcher at zero to the zero branch. This file contains no proof.
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

val nat_axiom_match_nat_type_O =
  ``!(case_O : 'a) (case_S : num -> 'a).
      logipedia_connectives_equal
        (logipedia_nat_match_nat_type case_O case_S 0)
        case_O``;
