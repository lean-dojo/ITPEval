(*
  Statement-only formalization of Logipedia corpus artifact
  leibniz.sym_leibniz (catalog title "leibniz.sym_leibniz"): Leibniz equality
  is symmetric over every type. This file contains no proof.
*)

Definition leibniz (A : Type) (x y : A) : Prop :=
  forall P : A -> Prop, P x -> P y.

Theorem sym_leibniz :
  forall (A : Type) (x y : A),
    leibniz A x y ->
    leibniz A y x.
Admitted.
