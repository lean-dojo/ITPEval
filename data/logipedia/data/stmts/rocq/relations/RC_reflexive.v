(*
  Statement-only formalization of Logipedia corpus artifact
  relations.RC_reflexive (catalog title "relations.RC_reflexive"): for every
  type and binary relation, its reflexive closure obtained by adjoining
  equality is reflexive. This file contains no proof.
*)

Definition relations_reflexive
    (A : Type) (R : A -> A -> Prop) : Prop :=
  forall x : A, R x x.

Definition relations_RC
    (A : Type) (R : A -> A -> Prop) : A -> A -> Prop :=
  fun x y => R x y \/ x = y.

Theorem RC_reflexive :
  forall (A : Type) (R : A -> A -> Prop),
    relations_reflexive A (relations_RC A R).
Admitted.
