(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1077462
  (thousand-theorems__rocq__Q1077462), "König's theorem (set theory)":
  for arbitrary type-indexed families, pointwise strict cardinal inequalities
  imply that the dependent sum of the smaller family has strictly smaller
  cardinality than the dependent product of the larger family. This file
  contains no proof.
*)

Set Universe Polymorphism.

Definition q1077462_injective
    {A B : Type} (f : A -> B) : Prop :=
  forall x y : A, f x = f y -> x = y.

Definition q1077462_card_le (A B : Type) : Prop :=
  exists f : A -> B, q1077462_injective f.

Definition q1077462_card_lt (A B : Type) : Prop :=
  q1077462_card_le A B /\ ~ q1077462_card_le B A.

Definition q1077462_cardinal_sum
    {I : Type} (A : I -> Type) : Type :=
  { i : I & A i }.

Definition q1077462_cardinal_product
    {I : Type} (B : I -> Type) : Type :=
  forall i : I, B i.

Theorem Cardinal_sum_lt_prod :
  forall (I : Type) (A B : I -> Type),
    (forall i : I, q1077462_card_lt (A i) (B i)) ->
    q1077462_card_lt
      (q1077462_cardinal_sum A)
      (q1077462_cardinal_product B).
Admitted.
