(*
  Statement-only formalization of the Logipedia corpus artifact
  connectives.refl_equal (catalog title "connectives.refl_equal"): the
  module's abstract equality relation is reflexive on every type. This file
  contains no proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_connectives_equal",
  Type.alpha --> Type.alpha --> Type.bool);

val connectives_refl_equal =
  ``!x : 'a.
      logipedia_connectives_equal x x``;
