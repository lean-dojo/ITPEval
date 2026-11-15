(*
  Statement-only formalization of the Logipedia corpus artifact
  relations.RC_reflexive (catalog title "relations.RC_reflexive"): adjoining
  equality to any binary relation yields a reflexive relation on every type.
  This file contains no proof.
*)

open HolKernel Parse boolLib;

val logipedia_relations_reflexive_def = new_definition (
  "logipedia_relations_reflexive_def",
  ``logipedia_relations_reflexive (R : 'a -> 'a -> bool) <=>
      !x : 'a. R x x``);

val logipedia_relations_RC_def = new_definition (
  "logipedia_relations_RC_def",
  ``logipedia_relations_RC (R : 'a -> 'a -> bool) (x : 'a) (y : 'a) <=>
      R x y \/ x = y``);

val relations_RC_reflexive =
  ``!(R : 'a -> 'a -> bool).
      logipedia_relations_reflexive (logipedia_relations_RC R)``;
