(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1457052
  (thousand-theorems__rocq__Q1457052), "Well-ordering theorem": every type
  admits a linear order whose strict relation is well-founded. This file
  contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1457052_linear_order (A : Type) : Type := {
  q1457052_le : A -> A -> Prop;
  q1457052_le_refl :
    forall x : A, q1457052_le x x;
  q1457052_le_trans :
    forall x y z : A,
      q1457052_le x y ->
      q1457052_le y z ->
      q1457052_le x z;
  q1457052_le_antisym :
    forall x y : A,
      q1457052_le x y ->
      q1457052_le y x ->
      x = y;
  q1457052_le_total :
    forall x y : A,
      q1457052_le x y \/ q1457052_le y x;
  q1457052_le_decidable :
    forall x y : A,
      {q1457052_le x y} + {~ q1457052_le x y}
}.

Arguments q1457052_le {A} _ _ _.

Definition q1457052_lt
    {A : Type} (O : q1457052_linear_order A) (x y : A) : Prop :=
  q1457052_le O x y /\ ~ q1457052_le O y x.

Theorem exists_wellOrder :
  forall A : Type,
    exists O : q1457052_linear_order A,
      well_founded (q1457052_lt O).
Admitted.
