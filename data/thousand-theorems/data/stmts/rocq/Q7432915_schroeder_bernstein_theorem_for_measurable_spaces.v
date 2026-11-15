(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7432915
  (thousand-theorems__rocq__Q7432915), "Schroeder–Bernstein theorem for
  measurable spaces": measurable embeddings in both directions between two
  measurable spaces yield a measurable equivalence. This file contains no
  proof.
*)

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Definition q7432915_set (A : Type) : Type := A -> Prop.

Definition q7432915_empty {A : Type} : q7432915_set A :=
  fun _ => False.

Definition q7432915_complement {A : Type}
    (E : q7432915_set A) : q7432915_set A :=
  fun x => ~ E x.

Definition q7432915_countable_union {A : Type}
    (E : nat -> q7432915_set A) : q7432915_set A :=
  fun x => exists n : nat, E n x.

Definition q7432915_same_set {A : Type}
    (E F : q7432915_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q7432915_image {A B : Type}
    (f : A -> B) (E : q7432915_set A) : q7432915_set B :=
  fun y => exists x : A, E x /\ f x = y.

Definition q7432915_preimage {A B : Type}
    (f : A -> B) (E : q7432915_set B) : q7432915_set A :=
  fun x => E (f x).

Record q7432915_measurable_space (A : Type) : Type := {
  q7432915_measurable_set : q7432915_set A -> Prop;
  q7432915_measurable_extensional :
    forall E F : q7432915_set A,
      q7432915_same_set E F ->
      (q7432915_measurable_set E <->
       q7432915_measurable_set F);
  q7432915_measurable_empty :
    q7432915_measurable_set q7432915_empty;
  q7432915_measurable_complement :
    forall E : q7432915_set A,
      q7432915_measurable_set E ->
      q7432915_measurable_set (q7432915_complement E);
  q7432915_measurable_countable_union :
    forall E : nat -> q7432915_set A,
      (forall n : nat, q7432915_measurable_set (E n)) ->
      q7432915_measurable_set (q7432915_countable_union E)
}.

Arguments q7432915_measurable_set {A} _ _.

Definition q7432915_measurable_map
    {A B : Type}
    (mA : q7432915_measurable_space A)
    (mB : q7432915_measurable_space B)
    (f : A -> B) : Prop :=
  forall E : q7432915_set B,
    q7432915_measurable_set mB E ->
    q7432915_measurable_set mA (q7432915_preimage f E).

Record q7432915_measurable_embedding
    {A B : Type}
    (mA : q7432915_measurable_space A)
    (mB : q7432915_measurable_space B)
    (f : A -> B) : Prop := {
  q7432915_embedding_injective :
    forall x y : A, f x = f y -> x = y;
  q7432915_embedding_measurable :
    q7432915_measurable_map mA mB f;
  q7432915_embedding_measurable_image :
    forall E : q7432915_set A,
      q7432915_measurable_set mA E ->
      q7432915_measurable_set mB (q7432915_image f E)
}.

Record q7432915_measurable_equiv
    {A B : Type}
    (mA : q7432915_measurable_space A)
    (mB : q7432915_measurable_space B) : Type := {
  q7432915_equiv_forward : A -> B;
  q7432915_equiv_backward : B -> A;
  q7432915_equiv_left_inverse :
    forall x : A,
      q7432915_equiv_backward (q7432915_equiv_forward x) = x;
  q7432915_equiv_right_inverse :
    forall y : B,
      q7432915_equiv_forward (q7432915_equiv_backward y) = y;
  q7432915_equiv_forward_measurable :
    q7432915_measurable_map
      mA mB q7432915_equiv_forward;
  q7432915_equiv_backward_measurable :
    q7432915_measurable_map
      mB mA q7432915_equiv_backward
}.

Theorem MeasurableEmbedding_schroederBernstein :
  forall (Alpha Beta : Type)
         (mAlpha : q7432915_measurable_space Alpha)
         (mBeta : q7432915_measurable_space Beta)
         (f : Alpha -> Beta)
         (g : Beta -> Alpha),
    q7432915_measurable_embedding mAlpha mBeta f ->
    q7432915_measurable_embedding mBeta mAlpha g ->
    q7432915_measurable_equiv mAlpha mBeta.
Admitted.
