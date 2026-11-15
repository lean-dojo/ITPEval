(*
  Statement-only formalization of the Logipedia corpus artifact logic.refl
  (catalog title "logic.refl"): the module's polymorphic abstract equality
  relation is reflexive at every element of every type. This file contains no
  proof.
*)

open HolKernel Parse boolLib;

val _ = new_constant (
  "logipedia_logic_eq",
  Type.alpha --> Type.alpha --> Type.bool);

val logic_refl =
  ``!x : 'a. logipedia_logic_eq x x``;
