(*
  Statement-only formalization of the Logipedia corpus artifact
  logic.sym_not_eq (catalog title "logic.sym_not_eq"): for elements of an
  arbitrary type, the module's abstract negation of equality in one direction
  entails its abstract negation in the reverse direction. This file contains
  no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_Not",
  Type.bool --> Type.bool);

val logic_sym_not_eq =
  ``!(x : 'a) (y : 'a).
      logipedia_connectives_Not (x = y) ==>
      logipedia_connectives_Not (y = x)``;
