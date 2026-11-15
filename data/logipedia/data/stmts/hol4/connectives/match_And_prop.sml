(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.match_And_prop (catalog title "connectives.match_And_prop"):
  for propositions A, B, and return, a handler from A and B to return,
  together with the module's abstract conjunction connectives.And A B,
  entails return. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_And",
  Type.bool --> Type.bool --> Type.bool);

val connectives_match_And_prop =
  ``!(A : bool) (B : bool) (return_ : bool).
      (A ==> B ==> return_) ==>
      logipedia_connectives_And A B ==>
      return_``;
