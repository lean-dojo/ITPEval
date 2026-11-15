(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.falsity (catalog title "connectives.falsity"): the elimination
  principle by which the module's abstract false proposition entails every
  proposition. This file contains no proof.
*)

Parameter connectives_False : Prop.

Theorem connectives_falsity :
  forall t : Prop,
    connectives_False ->
    t.
Admitted.
