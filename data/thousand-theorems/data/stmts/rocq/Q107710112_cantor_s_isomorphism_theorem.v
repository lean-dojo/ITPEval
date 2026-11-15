(*
  Statement-only formalization of Thousand Theorems corpus artifact Q107710112
  (thousand-theorems__rocq__Q107710112), "Cantor's isomorphism theorem":
  any two countable, dense, nonempty linear orders without endpoints are
  order isomorphic. This file contains no proof.
*)

Set Universe Polymorphism.
Set Implicit Arguments.

Record q107710112_linear_order (A : Type) : Type := {
  q107710112_lt : A -> A -> Prop;
  q107710112_lt_irrefl :
    forall x : A, ~ q107710112_lt x x;
  q107710112_lt_trans :
    forall x y z : A,
      q107710112_lt x y ->
      q107710112_lt y z ->
      q107710112_lt x z;
  q107710112_lt_trichotomy :
    forall x y : A,
      q107710112_lt x y \/ x = y \/ q107710112_lt y x
}.

Arguments q107710112_lt {A} _ _ _.

Definition q107710112_countable (A : Type) : Prop :=
  exists encode : A -> nat,
    forall x y : A, encode x = encode y -> x = y.

Definition q107710112_dense
    {A : Type} (O : q107710112_linear_order A) : Prop :=
  forall x y : A,
    q107710112_lt O x y ->
    exists z : A,
      q107710112_lt O x z /\ q107710112_lt O z y.

Definition q107710112_no_minimum
    {A : Type} (O : q107710112_linear_order A) : Prop :=
  forall x : A, exists y : A, q107710112_lt O y x.

Definition q107710112_no_maximum
    {A : Type} (O : q107710112_linear_order A) : Prop :=
  forall x : A, exists y : A, q107710112_lt O x y.

Definition q107710112_nonempty (A : Type) : Prop :=
  exists x : A, True.

Definition q107710112_order_isomorphic
    {A B : Type}
    (OA : q107710112_linear_order A)
    (OB : q107710112_linear_order B) : Prop :=
  exists forward : A -> B, exists backward : B -> A,
    (forall x : A, backward (forward x) = x) /\
    (forall y : B, forward (backward y) = y) /\
    (forall x y : A,
      q107710112_lt OA x y <->
      q107710112_lt OB (forward x) (forward y)).

Theorem iso_of_countable_dense :
  forall (A B : Type)
         (OA : q107710112_linear_order A)
         (OB : q107710112_linear_order B),
    q107710112_countable A ->
    q107710112_dense OA ->
    q107710112_no_minimum OA ->
    q107710112_no_maximum OA ->
    q107710112_nonempty A ->
    q107710112_countable B ->
    q107710112_dense OB ->
    q107710112_no_minimum OB ->
    q107710112_no_maximum OB ->
    q107710112_nonempty B ->
    q107710112_order_isomorphic OA OB.
Admitted.
