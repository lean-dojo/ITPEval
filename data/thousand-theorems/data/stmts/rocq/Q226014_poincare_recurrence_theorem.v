(*
  Statement-only formalization of Thousand Theorems corpus artifact Q226014
  (thousand-theorems__rocq__Q226014), "Poincaré recurrence theorem": for a
  conservative measurable dynamical system, almost every point of a
  null-measurable set returns to that set infinitely often. This file contains
  no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q226014_set (A : Type) : Type := A -> Prop.

Definition q226014_empty {A : Type} : q226014_set A :=
  fun _ => False.

Definition q226014_complement {A : Type}
    (E : q226014_set A) : q226014_set A :=
  fun x => ~ E x.

Definition q226014_union {A : Type}
    (E F : q226014_set A) : q226014_set A :=
  fun x => E x \/ F x.

Definition q226014_countable_union {A : Type}
    (E : nat -> q226014_set A) : q226014_set A :=
  fun x => exists n : nat, E n x.

Definition q226014_preimage {A B : Type}
    (f : A -> B) (E : q226014_set B) : q226014_set A :=
  fun x => E (f x).

Definition q226014_same_set {A : Type}
    (E F : q226014_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q226014_disjoint {A : Type}
    (E F : q226014_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q226014_pairwise_disjoint {A : Type}
    (E : nat -> q226014_set A) : Prop :=
  forall i j : nat,
    i <> j ->
    q226014_disjoint (E i) (E j).

Definition q226014_symmetric_difference {A : Type}
    (E F : q226014_set A) : q226014_set A :=
  fun x => (E x /\ ~ F x) \/ (F x /\ ~ E x).

Inductive q226014_ennreal : Type :=
| q226014_ennreal_finite :
    forall value : R, 0 <= value -> q226014_ennreal
| q226014_ennreal_infinity : q226014_ennreal.

Arguments q226014_ennreal_finite value nonnegative : clear implicits.

Definition q226014_ennreal_zero : q226014_ennreal :=
  q226014_ennreal_finite 0 (Rle_refl 0).

Definition q226014_ennreal_equiv
    (x y : q226014_ennreal) : Prop :=
  match x, y with
  | q226014_ennreal_finite a _,
    q226014_ennreal_finite b _ => a = b
  | q226014_ennreal_infinity,
    q226014_ennreal_infinity => True
  | _, _ => False
  end.

Definition q226014_ennreal_le
    (x y : q226014_ennreal) : Prop :=
  match x, y with
  | q226014_ennreal_finite a _,
    q226014_ennreal_finite b _ => a <= b
  | q226014_ennreal_finite _ _,
    q226014_ennreal_infinity => True
  | q226014_ennreal_infinity,
    q226014_ennreal_finite _ _ => False
  | q226014_ennreal_infinity,
    q226014_ennreal_infinity => True
  end.

Definition q226014_ennreal_add
    (x y : q226014_ennreal) : q226014_ennreal :=
  match x, y with
  | q226014_ennreal_finite a ha,
    q226014_ennreal_finite b hb =>
      q226014_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q226014_ennreal_infinity
  end.

Fixpoint q226014_ennreal_partial_sum
    (u : nat -> q226014_ennreal) (n : nat) : q226014_ennreal :=
  match n with
  | O => q226014_ennreal_zero
  | S k =>
      q226014_ennreal_add
        (q226014_ennreal_partial_sum u k) (u k)
  end.

Definition q226014_ennreal_supremum
    (values : q226014_ennreal -> Prop)
    (bound : q226014_ennreal) : Prop :=
  (forall value : q226014_ennreal,
      values value ->
      q226014_ennreal_le value bound) /\
  (forall upper : q226014_ennreal,
      (forall value : q226014_ennreal,
          values value ->
          q226014_ennreal_le value upper) ->
      q226014_ennreal_le bound upper).

Definition q226014_ennreal_infimum
    (values : q226014_ennreal -> Prop)
    (bound : q226014_ennreal) : Prop :=
  (forall value : q226014_ennreal,
      values value ->
      q226014_ennreal_le bound value) /\
  (forall lower : q226014_ennreal,
      (forall value : q226014_ennreal,
          values value ->
          q226014_ennreal_le lower value) ->
      q226014_ennreal_le lower bound).

Definition q226014_ennreal_series_sum
    (u : nat -> q226014_ennreal)
    (total : q226014_ennreal) : Prop :=
  q226014_ennreal_supremum
    (fun value =>
      exists n : nat,
        q226014_ennreal_equiv
          value (q226014_ennreal_partial_sum u n))
    total.

Record q226014_measurable_space (A : Type) : Type := {
  q226014_measurable : q226014_set A -> Prop;
  q226014_measurable_extensional :
    forall E F : q226014_set A,
      q226014_same_set E F ->
      (q226014_measurable E <-> q226014_measurable F);
  q226014_measurable_empty :
    q226014_measurable q226014_empty;
  q226014_measurable_complement :
    forall E : q226014_set A,
      q226014_measurable E ->
      q226014_measurable (q226014_complement E);
  q226014_measurable_countable_union :
    forall E : nat -> q226014_set A,
      (forall n : nat, q226014_measurable (E n)) ->
      q226014_measurable (q226014_countable_union E)
}.

Arguments q226014_measurable {A} _ _.

Record q226014_measure
    (A : Type) (M : q226014_measurable_space A) : Type := {
  q226014_measure_value :
    q226014_set A -> q226014_ennreal;
  q226014_measure_extensional :
    forall E F : q226014_set A,
      q226014_same_set E F ->
      q226014_ennreal_equiv
        (q226014_measure_value E)
        (q226014_measure_value F);
  q226014_measure_empty :
    q226014_ennreal_equiv
      (q226014_measure_value q226014_empty)
      q226014_ennreal_zero;
  q226014_measure_monotone :
    forall E F : q226014_set A,
      (forall x : A, E x -> F x) ->
      q226014_ennreal_le
        (q226014_measure_value E)
        (q226014_measure_value F);
  q226014_measure_canonical_outer_extension :
    forall E : q226014_set A,
      q226014_ennreal_infimum
        (fun value =>
          exists measurable_superset : q226014_set A,
            (forall x : A, E x -> measurable_superset x) /\
            q226014_measurable M measurable_superset /\
            q226014_ennreal_equiv
              value (q226014_measure_value measurable_superset))
        (q226014_measure_value E);
  q226014_measure_countable_subadditive :
    forall (E : nat -> q226014_set A)
           (total : q226014_ennreal),
      q226014_ennreal_series_sum
        (fun n => q226014_measure_value (E n)) total ->
      q226014_ennreal_le
        (q226014_measure_value (q226014_countable_union E))
        total;
  q226014_measure_countable_additive :
    forall E : nat -> q226014_set A,
      (forall n : nat, q226014_measurable M (E n)) ->
      q226014_pairwise_disjoint E ->
      q226014_ennreal_series_sum
        (fun n => q226014_measure_value (E n))
        (q226014_measure_value (q226014_countable_union E))
}.

Arguments q226014_measure_value {A M} _ _.

Definition q226014_measurable_map
    {A B : Type}
    (MA : q226014_measurable_space A)
    (MB : q226014_measurable_space B)
    (f : A -> B) : Prop :=
  forall E : q226014_set B,
    q226014_measurable MB E ->
    q226014_measurable MA (q226014_preimage f E).

Definition q226014_null_measurable_set
    {A : Type}
    (M : q226014_measurable_space A)
    (mu : @q226014_measure A M)
    (E : q226014_set A) : Prop :=
  exists measurable_version : q226014_set A,
    q226014_measurable M measurable_version /\
    q226014_ennreal_equiv
      (q226014_measure_value mu
        (q226014_symmetric_difference E measurable_version))
      q226014_ennreal_zero.

Definition q226014_quasi_measure_preserving
    {A : Type}
    (M : q226014_measurable_space A)
    (mu : @q226014_measure A M)
    (f : A -> A) : Prop :=
  q226014_measurable_map M M f /\
  forall E : q226014_set A,
    q226014_ennreal_equiv
      (q226014_measure_value mu E)
      q226014_ennreal_zero ->
    q226014_ennreal_equiv
      (q226014_measure_value mu (q226014_preimage f E))
      q226014_ennreal_zero.

Fixpoint q226014_iterate
    {A : Type} (f : A -> A) (n : nat) (x : A) : A :=
  match n with
  | O => x
  | S k => f (q226014_iterate f k x)
  end.

Definition q226014_frequently_at_top
    (P : nat -> Prop) : Prop :=
  forall lower_bound : nat,
    exists n : nat,
      (lower_bound <= n)%nat /\ P n.

Definition q226014_almost_everywhere
    {A : Type}
    {M : q226014_measurable_space A}
    (mu : @q226014_measure A M)
    (P : A -> Prop) : Prop :=
  q226014_ennreal_equiv
    (q226014_measure_value mu (fun x => ~ P x))
    q226014_ennreal_zero.

Definition q226014_conservative
    {A : Type}
    (M : q226014_measurable_space A)
    (mu : @q226014_measure A M)
    (f : A -> A) : Prop :=
  @q226014_quasi_measure_preserving A M mu f /\
  forall E : q226014_set A,
    q226014_measurable M E ->
    ~ q226014_ennreal_equiv
        (q226014_measure_value mu E)
        q226014_ennreal_zero ->
    exists x : A,
      E x /\
      exists n : nat,
        n <> O /\
        E (q226014_iterate f n x).

Theorem q226014_poincare_recurrence_theorem :
  forall (A : Type)
         (M : q226014_measurable_space A)
         (f : A -> A)
         (s : q226014_set A)
         (mu : @q226014_measure A M),
    @q226014_conservative A M mu f ->
    @q226014_null_measurable_set A M mu s ->
    q226014_almost_everywhere mu
      (fun x =>
        s x ->
        q226014_frequently_at_top
          (fun n => s (q226014_iterate f n x))).
Admitted.
