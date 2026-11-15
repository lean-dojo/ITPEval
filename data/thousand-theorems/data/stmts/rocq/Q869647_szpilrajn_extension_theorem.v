(*
  Statement-only formalization of Thousand Theorems corpus artifact Q869647
  (thousand-theorems__rocq__Q869647), "Szpilrajn extension theorem": every
  partial order on an arbitrary type extends to a linear order. This file
  contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Definition q869647_is_partial_order
    {A : Type} (r : A -> A -> Prop) : Prop :=
  (forall x : A, r x x) /\
  (forall x y z : A, r x y -> r y z -> r x z) /\
  (forall x y : A, r x y -> r y x -> x = y).

Definition q869647_is_linear_order
    {A : Type} (r : A -> A -> Prop) : Prop :=
  q869647_is_partial_order r /\
  forall x y : A, r x y \/ r y x.

Theorem extend_partialOrder :
  forall (A : Type) (r : A -> A -> Prop),
    q869647_is_partial_order r ->
    exists s : A -> A -> Prop,
      q869647_is_linear_order s /\
      forall x y : A, r x y -> s x y.
Admitted.
