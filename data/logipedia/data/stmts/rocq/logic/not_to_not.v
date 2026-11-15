(*
  Statement-only formalization of Logipedia corpus artifact logic.not_to_not
  (catalog title "logic.not_to_not"): an implication from one proposition to
  another transports the latter's abstract negation to the former. This file
  contains no proof.
*)

Parameter connectives_Not : Prop -> Prop.

Theorem logic_not_to_not :
  forall A B : Prop,
    (A -> B) ->
    connectives_Not B ->
    connectives_Not A.
Admitted.
