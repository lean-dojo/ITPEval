(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2631152
  (thousand-theorems__rocq__Q2631152), "Carathéodory's extension theorem":
  the measure induced by a sigma-subadditive extended-nonnegative additive
  content on a semiring agrees with that content on every semiring set when
  the semiring generates the ambient measurable space. This file contains no
  proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q2631152_set (A : Type) : Type := A -> Prop.

Definition q2631152_empty {A : Type} : q2631152_set A :=
  fun _ => False.

Definition q2631152_complement {A : Type}
    (E : q2631152_set A) : q2631152_set A :=
  fun x => ~ E x.

Definition q2631152_intersection {A : Type}
    (E F : q2631152_set A) : q2631152_set A :=
  fun x => E x /\ F x.

Definition q2631152_difference {A : Type}
    (E F : q2631152_set A) : q2631152_set A :=
  fun x => E x /\ ~ F x.

Definition q2631152_countable_union {A : Type}
    (E : nat -> q2631152_set A) : q2631152_set A :=
  fun x => exists n : nat, E n x.

Definition q2631152_finite_union {A : Type}
    (n : nat) (E : nat -> q2631152_set A) : q2631152_set A :=
  fun x => exists i : nat, (i < n)%nat /\ E i x.

Definition q2631152_same_set {A : Type}
    (E F : q2631152_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q2631152_subset {A : Type}
    (E F : q2631152_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q2631152_disjoint {A : Type}
    (E F : q2631152_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q2631152_pairwise_disjoint_below {A : Type}
    (n : nat) (E : nat -> q2631152_set A) : Prop :=
  forall i j : nat,
    (i < n)%nat ->
    (j < n)%nat ->
    i <> j ->
    q2631152_disjoint (E i) (E j).

Definition q2631152_distinct_below {A : Type}
    (n : nat) (E : nat -> q2631152_set A) : Prop :=
  forall i j : nat,
    (i < n)%nat ->
    (j < n)%nat ->
    q2631152_same_set (E i) (E j) ->
    i = j.

Inductive q2631152_ennreal : Type :=
| q2631152_ennreal_finite :
    forall value : R, 0 <= value -> q2631152_ennreal
| q2631152_ennreal_infinity : q2631152_ennreal.

Arguments q2631152_ennreal_finite value nonnegative : clear implicits.

Definition q2631152_ennreal_zero : q2631152_ennreal :=
  q2631152_ennreal_finite 0 (Rle_refl 0).

Definition q2631152_ennreal_eq
    (x y : q2631152_ennreal) : Prop :=
  match x, y with
  | q2631152_ennreal_finite a _,
    q2631152_ennreal_finite b _ => a = b
  | q2631152_ennreal_infinity,
    q2631152_ennreal_infinity => True
  | _, _ => False
  end.

Definition q2631152_ennreal_le
    (x y : q2631152_ennreal) : Prop :=
  match x, y with
  | q2631152_ennreal_finite a _,
    q2631152_ennreal_finite b _ => a <= b
  | q2631152_ennreal_finite _ _,
    q2631152_ennreal_infinity => True
  | q2631152_ennreal_infinity,
    q2631152_ennreal_finite _ _ => False
  | q2631152_ennreal_infinity,
    q2631152_ennreal_infinity => True
  end.

Definition q2631152_ennreal_add
    (x y : q2631152_ennreal) : q2631152_ennreal :=
  match x, y with
  | q2631152_ennreal_finite a ha,
    q2631152_ennreal_finite b hb =>
      q2631152_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q2631152_ennreal_infinity
  end.

Fixpoint q2631152_ennreal_partial_sum
    (u : nat -> q2631152_ennreal)
    (n : nat) : q2631152_ennreal :=
  match n with
  | O => q2631152_ennreal_zero
  | S k =>
      q2631152_ennreal_add
        (q2631152_ennreal_partial_sum u k) (u k)
  end.

Definition q2631152_ennreal_supremum
    (values : q2631152_ennreal -> Prop)
    (bound : q2631152_ennreal) : Prop :=
  (forall value : q2631152_ennreal,
      values value -> q2631152_ennreal_le value bound) /\
  (forall upper : q2631152_ennreal,
      (forall value : q2631152_ennreal,
        values value -> q2631152_ennreal_le value upper) ->
      q2631152_ennreal_le bound upper).

Definition q2631152_ennreal_infimum
    (values : q2631152_ennreal -> Prop)
    (bound : q2631152_ennreal) : Prop :=
  (forall value : q2631152_ennreal,
      values value -> q2631152_ennreal_le bound value) /\
  (forall lower : q2631152_ennreal,
      (forall value : q2631152_ennreal,
        values value -> q2631152_ennreal_le lower value) ->
      q2631152_ennreal_le lower bound).

Definition q2631152_ennreal_series_sum
    (u : nat -> q2631152_ennreal)
    (sum : q2631152_ennreal) : Prop :=
  q2631152_ennreal_supremum
    (fun value =>
      exists n : nat,
        q2631152_ennreal_eq value
          (q2631152_ennreal_partial_sum u n))
    sum.

Definition q2631152_ennreal_finite_sum
    {A : Type}
    (m : q2631152_set A -> q2631152_ennreal)
    (E : nat -> q2631152_set A)
    (n : nat) : q2631152_ennreal :=
  q2631152_ennreal_partial_sum (fun i => m (E i)) n.

Record q2631152_set_semiring
    (A : Type) (C : q2631152_set (q2631152_set A)) : Prop := {
  q2631152_semiring_extensional :
    forall E F : q2631152_set A,
      q2631152_same_set E F ->
      C E ->
      C F;
  q2631152_semiring_empty :
    C q2631152_empty;
  q2631152_semiring_intersection :
    forall E F : q2631152_set A,
      C E ->
      C F ->
      C (q2631152_intersection E F);
  q2631152_semiring_difference :
    forall E F : q2631152_set A,
      C E ->
      C F ->
      exists (n : nat) (pieces : nat -> q2631152_set A),
        q2631152_distinct_below n pieces /\
        (forall i : nat, (i < n)%nat -> C (pieces i)) /\
        q2631152_pairwise_disjoint_below n pieces /\
        q2631152_same_set
          (q2631152_difference E F)
          (q2631152_finite_union n pieces)
}.

Record q2631152_add_content
    (A : Type) (C : q2631152_set (q2631152_set A)) : Type := {
  q2631152_content_value :
    q2631152_set A -> q2631152_ennreal;
  q2631152_content_extensional :
    forall E F : q2631152_set A,
      q2631152_same_set E F ->
      q2631152_ennreal_eq
        (q2631152_content_value E)
        (q2631152_content_value F);
  q2631152_content_empty :
    q2631152_ennreal_eq
      (q2631152_content_value q2631152_empty)
      q2631152_ennreal_zero;
  q2631152_content_finitely_additive :
    forall (n : nat) (E : nat -> q2631152_set A),
      q2631152_distinct_below n E ->
      (forall i : nat, (i < n)%nat -> C (E i)) ->
      q2631152_pairwise_disjoint_below n E ->
      C (q2631152_finite_union n E) ->
      q2631152_ennreal_eq
        (q2631152_content_value
          (q2631152_finite_union n E))
        (q2631152_ennreal_finite_sum
          q2631152_content_value E n)
}.

Arguments q2631152_content_value {A C} _ _.

Definition q2631152_sigma_subadditive
    {A : Type} {C : q2631152_set (q2631152_set A)}
    (m : @q2631152_add_content A C) : Prop :=
  forall E : nat -> q2631152_set A,
    (forall n : nat, C (E n)) ->
    C (q2631152_countable_union E) ->
    exists total : q2631152_ennreal,
      q2631152_ennreal_series_sum
        (fun n => q2631152_content_value m (E n))
        total /\
      q2631152_ennreal_le
        (q2631152_content_value m
          (q2631152_countable_union E))
        total.

Record q2631152_measurable_space (A : Type) : Type := {
  q2631152_measurable : q2631152_set A -> Prop;
  q2631152_measurable_extensional :
    forall E F : q2631152_set A,
      q2631152_same_set E F ->
      (q2631152_measurable E <-> q2631152_measurable F);
  q2631152_measurable_empty :
    q2631152_measurable q2631152_empty;
  q2631152_measurable_complement :
    forall E : q2631152_set A,
      q2631152_measurable E ->
      q2631152_measurable (q2631152_complement E);
  q2631152_measurable_countable_union :
    forall E : nat -> q2631152_set A,
      (forall n : nat, q2631152_measurable (E n)) ->
      q2631152_measurable (q2631152_countable_union E)
}.

Arguments q2631152_measurable {A} _ _.

Inductive q2631152_generated_measurable
    {A : Type}
    (C : q2631152_set (q2631152_set A))
    : q2631152_set A -> Prop :=
| q2631152_generated_basic :
    forall E : q2631152_set A,
      C E ->
      q2631152_generated_measurable C E
| q2631152_generated_empty :
    q2631152_generated_measurable C q2631152_empty
| q2631152_generated_extensional :
    forall E F : q2631152_set A,
      q2631152_generated_measurable C E ->
      q2631152_same_set E F ->
      q2631152_generated_measurable C F
| q2631152_generated_complement :
    forall E : q2631152_set A,
      q2631152_generated_measurable C E ->
      q2631152_generated_measurable C
        (q2631152_complement E)
| q2631152_generated_countable_union :
    forall E : nat -> q2631152_set A,
      (forall n : nat, q2631152_generated_measurable C (E n)) ->
      q2631152_generated_measurable C
        (q2631152_countable_union E).

Definition q2631152_is_generated_by
    {A : Type}
    (M : q2631152_measurable_space A)
    (C : q2631152_set (q2631152_set A)) : Prop :=
  forall E : q2631152_set A,
    q2631152_measurable M E <->
    q2631152_generated_measurable C E.

Definition q2631152_cover_cost
    {A : Type} {C : q2631152_set (q2631152_set A)}
    (m : @q2631152_add_content A C)
    (S : q2631152_set A)
    (cost : q2631152_ennreal) : Prop :=
  exists cover : nat -> q2631152_set A,
    (forall n : nat, C (cover n)) /\
    q2631152_subset S (q2631152_countable_union cover) /\
    q2631152_ennreal_series_sum
      (fun n => q2631152_content_value m (cover n))
      cost.

Definition q2631152_induced_outer_measure_has_value
    {A : Type} {C : q2631152_set (q2631152_set A)}
    (m : @q2631152_add_content A C)
    (S : q2631152_set A)
    (value : q2631152_ennreal) : Prop :=
  q2631152_ennreal_infimum
    (q2631152_cover_cost m S)
    value.

Definition q2631152_generated_measure_has_value
    {A : Type} {C : q2631152_set (q2631152_set A)}
    (_M : q2631152_measurable_space A)
    (m : @q2631152_add_content A C)
    (S : q2631152_set A)
    (value : q2631152_ennreal) : Prop :=
  q2631152_induced_outer_measure_has_value m S value.

Theorem MeasureTheory_AddContent_measure_eq :
  forall (Alpha : Type)
         (C : q2631152_set (q2631152_set Alpha))
         (M : q2631152_measurable_space Alpha)
         (m : @q2631152_add_content Alpha C)
         (S : q2631152_set Alpha),
    @q2631152_set_semiring Alpha C ->
    q2631152_is_generated_by M C ->
    q2631152_sigma_subadditive m ->
    C S ->
    exists value : q2631152_ennreal,
      q2631152_generated_measure_has_value M m S value /\
      q2631152_ennreal_eq
        value (q2631152_content_value m S).
Admitted.
