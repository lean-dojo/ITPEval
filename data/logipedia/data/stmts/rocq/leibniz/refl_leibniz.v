(*
  Statement-only formalization of Logipedia corpus artifact
  leibniz.refl_leibniz (catalog title "leibniz.refl_leibniz"): every element
  of every type is Leibniz-equal to itself. This file contains no proof.
*)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Theorem refl_leibniz :
  forall (A : Type) (x : A),
    leibniz A x x.
Admitted.
