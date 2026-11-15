(*
  Statement-only formalization of the Logipedia corpus artifact connectives.I
  (catalog title "connectives.I"): the module's distinguished abstract
  proposition connectives.True holds. This file contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_True",
  Type.bool);

val connectives_I =
  ``logipedia_connectives_True``;
