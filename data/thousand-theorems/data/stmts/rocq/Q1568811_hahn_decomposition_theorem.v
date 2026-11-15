(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1568811
  (thousand-theorems__rocq__Q1568811), "Hahn decomposition theorem": every
  real-valued signed measure on a measurable space admits complementary
  measurable positive and negative sets. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1568811_set (A : Type) : Type := A -> Prop.

Definition q1568811_empty {A : Type} : q1568811_set A :=
  fun _ => False.

Definition q1568811_complement {A : Type}
    (E : q1568811_set A) : q1568811_set A :=
  fun x => ~ E x.

Definition q1568811_countable_union {A : Type}
    (E : nat -> q1568811_set A) : q1568811_set A :=
  fun x => exists n : nat, E n x.

Definition q1568811_same_set {A : Type}
    (E F : q1568811_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1568811_subset {A : Type}
    (E F : q1568811_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q1568811_disjoint {A : Type}
    (E F : q1568811_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1568811_pairwise_disjoint {A : Type}
    (E : nat -> q1568811_set A) : Prop :=
  forall i j : nat, i <> j -> q1568811_disjoint (E i) (E j).

Record q1568811_measurable_space (A : Type) : Type := {
  q1568811_measurable : q1568811_set A -> Prop;
  q1568811_measurable_extensional :
    forall E F : q1568811_set A,
      q1568811_same_set E F ->
      (q1568811_measurable E <-> q1568811_measurable F);
  q1568811_measurable_empty :
    q1568811_measurable q1568811_empty;
  q1568811_measurable_complement :
    forall E : q1568811_set A,
      q1568811_measurable E ->
      q1568811_measurable (q1568811_complement E);
  q1568811_measurable_countable_union :
    forall E : nat -> q1568811_set A,
      (forall n : nat, q1568811_measurable (E n)) ->
      q1568811_measurable (q1568811_countable_union E)
}.

Arguments q1568811_measurable {A} _ _.

Fixpoint q1568811_partial_sum
    (u : nat -> R) (n : nat) : R :=
  match n with
  | O => 0
  | S k => q1568811_partial_sum u k + u k
  end.

Definition q1568811_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Record q1568811_signed_measure (A : Type)
    (m : q1568811_measurable_space A) : Type := {
  q1568811_signed_measure_value : q1568811_set A -> R;
  q1568811_signed_measure_extensional :
    forall E F : q1568811_set A,
      q1568811_same_set E F ->
      q1568811_signed_measure_value E =
      q1568811_signed_measure_value F;
  q1568811_signed_measure_empty :
    q1568811_signed_measure_value q1568811_empty = 0;
  q1568811_signed_measure_nonmeasurable :
    forall E : q1568811_set A,
      ~ q1568811_measurable m E ->
      q1568811_signed_measure_value E = 0;
  q1568811_signed_measure_countable_additive :
    forall E : nat -> q1568811_set A,
      (forall n : nat, q1568811_measurable m (E n)) ->
      q1568811_pairwise_disjoint E ->
      q1568811_real_sequence_converges
        (fun n =>
          q1568811_partial_sum
            (fun k => q1568811_signed_measure_value (E k)) n)
        (q1568811_signed_measure_value
          (q1568811_countable_union E))
}.

Arguments q1568811_signed_measure_value {A m} _ _.

Definition q1568811_positive_on {A : Type}
    {m : q1568811_measurable_space A}
    (s : q1568811_signed_measure m)
    (i : q1568811_set A) : Prop :=
  forall E : q1568811_set A,
    q1568811_measurable m E ->
    q1568811_subset E i ->
    0 <= q1568811_signed_measure_value s E.

Definition q1568811_negative_on {A : Type}
    {m : q1568811_measurable_space A}
    (s : q1568811_signed_measure m)
    (i : q1568811_set A) : Prop :=
  forall E : q1568811_set A,
    q1568811_measurable m E ->
    q1568811_subset E i ->
    q1568811_signed_measure_value s E <= 0.

Definition q1568811_is_complement {A : Type}
    (i j : q1568811_set A) : Prop :=
  q1568811_disjoint i j /\
  forall x : A, i x \/ j x.

Theorem exists_isCompl_positive_negative :
  forall (Alpha : Type)
         (m : q1568811_measurable_space Alpha)
         (s : q1568811_signed_measure m),
    exists i j : q1568811_set Alpha,
      q1568811_measurable m i /\
      q1568811_positive_on s i /\
      q1568811_measurable m j /\
      q1568811_negative_on s j /\
      q1568811_is_complement i j.
Admitted.
