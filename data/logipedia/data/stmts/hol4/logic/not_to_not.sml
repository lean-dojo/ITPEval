(*
  Statement-only formalization of the Logipedia corpus artifact
  logic.not_to_not (catalog title "logic.not_to_not"): for arbitrary
  propositions A and B, an implication from A to B together with the module's
  abstract negation of B entails its abstract negation of A. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_Not",
  Type.bool --> Type.bool);

val logic_not_to_not =
  ``!(A : bool) (B : bool).
      (A ==> B) ==>
      logipedia_connectives_Not B ==>
      logipedia_connectives_Not A``;
