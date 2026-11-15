(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.or_introl (catalog title "connectives.or_introl"): for any
  propositions A and B, assumption A entails the module's abstract
  disjunction connectives.Or A B. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_Or",
  Type.bool --> Type.bool --> Type.bool);

val connectives_or_introl =
  ``!(A : bool) (B : bool).
      A ==>
      logipedia_connectives_Or A B``;
