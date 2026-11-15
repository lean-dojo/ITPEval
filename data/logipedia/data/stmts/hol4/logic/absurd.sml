(*
  Statement-only formalization of the Logipedia corpus artifact logic.absurd
  (catalog title "logic.absurd"): for every proposition A, A together with
  the module's abstract negation of A entails the module's abstract falsity
  proposition. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_False",
  Type.bool);

val _ = new_constant (
  "logipedia_connectives_Not",
  Type.bool --> Type.bool);

val logic_absurd =
  ``!A : bool.
      A ==>
      logipedia_connectives_Not A ==>
      logipedia_connectives_False``;
