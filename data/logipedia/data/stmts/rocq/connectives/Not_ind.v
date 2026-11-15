(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.Not_ind (catalog title "connectives.Not_ind"): the elimination
  principle for an abstract negation connective relative to an abstract false
  proposition. This file contains no proof.
*)

Parameter connectives_False : Prop.
Parameter connectives_Not : Prop -> Prop.

Theorem connectives_Not_ind :
  forall (A : Prop), forall (Q : Prop),
    ((A -> connectives_False) -> Q) ->
    connectives_Not A ->
    Q.
Admitted.
