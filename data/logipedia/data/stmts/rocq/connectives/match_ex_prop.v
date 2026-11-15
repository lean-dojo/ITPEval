(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.match_ex_prop (catalog title "connectives.match_ex_prop"):
  the elimination principle for the module's abstract existential connective
  over arbitrary types. This file contains no proof.
*)

Parameter connectives_ex : forall A : Type, (A -> Prop) -> Prop.

Theorem connectives_match_ex_prop :
  forall (A : Type), forall (P : A -> Prop), forall (return_ : Prop),
    (forall x : A, P x -> return_) ->
    connectives_ex A P ->
    return_.
Admitted.
