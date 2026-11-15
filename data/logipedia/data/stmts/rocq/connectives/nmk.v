(*
  Statement-only formalization of Logipedia corpus artifact connectives.nmk
  (catalog title "connectives.nmk"): the introduction principle for the
  module's abstract negation connective relative to its abstract false
  proposition. This file contains no proof.
*)

Parameter connectives_False : Prop.
Parameter connectives_Not : Prop -> Prop.

Theorem connectives_nmk :
  forall A : Prop,
    (A -> connectives_False) ->
    connectives_Not A.
Admitted.
