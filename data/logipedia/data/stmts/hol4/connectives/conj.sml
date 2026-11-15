(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.conj (catalog title "connectives.conj"): for any propositions A
  and B, assumptions A and B entail the module's abstract conjunction
  connectives.And A B. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_And",
  Type.bool --> Type.bool --> Type.bool);

val connectives_conj =
  ``!(A : bool) (B : bool).
      A ==>
      B ==>
      logipedia_connectives_And A B``;
