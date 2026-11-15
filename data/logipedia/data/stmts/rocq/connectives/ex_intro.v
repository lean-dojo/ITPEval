(*
  Statement-only formalization of Logipedia corpus artifact
  connectives.ex_intro (catalog title "connectives.ex_intro"): the introduction
  principle for the module's abstract existential connective over arbitrary
  types. This file contains no proof.
*)

Parameter connectives_ex : forall A : Type, (A -> Prop) -> Prop.

Theorem connectives_ex_intro :
  forall (A : Type), forall (P : A -> Prop), forall (x : A),
    P x ->
    connectives_ex A P.
Admitted.
