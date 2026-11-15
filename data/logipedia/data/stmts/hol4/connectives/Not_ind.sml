(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.Not_ind (catalog title "connectives.Not_ind"): for any
  propositions A and Q, an eliminator from A-implies-False into Q, together
  with abstract Not A, yields Q. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_False",
  Type.bool);

val _ = new_constant (
  "logipedia_connectives_Not",
  Type.bool --> Type.bool);

val connectives_Not_ind =
  ``!(A : bool) (Q : bool).
      ((A ==> logipedia_connectives_False) ==> Q) ==>
      logipedia_connectives_Not A ==>
      Q``;
