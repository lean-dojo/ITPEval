(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.match_Or_prop (catalog title "connectives.match_Or_prop"): for
  propositions A, B, and return, handlers from A and B to return, together
  with the module's abstract disjunction connectives.Or A B, entail return.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_Or",
  Type.bool --> Type.bool --> Type.bool);

val connectives_match_Or_prop =
  ``!(A : bool) (B : bool) (return_ : bool).
      (A ==> return_) ==>
      (B ==> return_) ==>
      logipedia_connectives_Or A B ==>
      return_``;
