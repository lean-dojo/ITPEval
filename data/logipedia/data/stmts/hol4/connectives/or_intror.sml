(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.or_intror (catalog title "connectives.or_intror"): for any
  propositions A and B, assumption B entails the module's abstract
  disjunction connectives.Or A B. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_Or",
  Type.bool --> Type.bool --> Type.bool);

val connectives_or_intror =
  ``!(A : bool) (B : bool).
      B ==>
      logipedia_connectives_Or A B``;
