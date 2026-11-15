(*
  Statement-only formalization of Thousand Theorems corpus artifact Q258374
  (thousand-theorems__rocq__Q258374), "Carathéodory's theorem (measure
  theory)": the subsets satisfying the Carathéodory splitting criterion for
  an outer measure form a measurable space. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q258374_set (A : Type) : Type := A -> Prop.

Definition q258374_empty {A : Type} : q258374_set A :=
  fun _ => False.

Definition q258374_complement {A : Type}
    (E : q258374_set A) : q258374_set A :=
  fun x => ~ E x.

Definition q258374_intersection {A : Type}
    (E F : q258374_set A) : q258374_set A :=
  fun x => E x /\ F x.

Definition q258374_difference {A : Type}
    (E F : q258374_set A) : q258374_set A :=
  fun x => E x /\ ~ F x.

Definition q258374_countable_union {A : Type}
    (E : nat -> q258374_set A) : q258374_set A :=
  fun x => exists n : nat, E n x.

Definition q258374_same_set {A : Type}
    (E F : q258374_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q258374_subset {A : Type}
    (E F : q258374_set A) : Prop :=
  forall x : A, E x -> F x.

Inductive q258374_ennreal : Type :=
| q258374_ennreal_finite :
    forall value : R, 0 <= value -> q258374_ennreal
| q258374_ennreal_infinity : q258374_ennreal.

Arguments q258374_ennreal_finite value nonnegative : clear implicits.

Definition q258374_ennreal_zero : q258374_ennreal :=
  q258374_ennreal_finite 0 (Rle_refl 0).

Definition q258374_ennreal_eq
    (x y : q258374_ennreal) : Prop :=
  match x, y with
  | q258374_ennreal_finite a _,
    q258374_ennreal_finite b _ => a = b
  | q258374_ennreal_infinity,
    q258374_ennreal_infinity => True
  | _, _ => False
  end.

Definition q258374_ennreal_le
    (x y : q258374_ennreal) : Prop :=
  match x, y with
  | q258374_ennreal_finite a _,
    q258374_ennreal_finite b _ => a <= b
  | q258374_ennreal_finite _ _,
    q258374_ennreal_infinity => True
  | q258374_ennreal_infinity,
    q258374_ennreal_finite _ _ => False
  | q258374_ennreal_infinity,
    q258374_ennreal_infinity => True
  end.

Definition q258374_ennreal_add
    (x y : q258374_ennreal) : q258374_ennreal :=
  match x, y with
  | q258374_ennreal_finite a ha,
    q258374_ennreal_finite b hb =>
      q258374_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q258374_ennreal_infinity
  end.

Fixpoint q258374_ennreal_partial_sum
    (u : nat -> q258374_ennreal)
    (n : nat) : q258374_ennreal :=
  match n with
  | O => q258374_ennreal_zero
  | S k =>
      q258374_ennreal_add
        (q258374_ennreal_partial_sum u k) (u k)
  end.

Definition q258374_ennreal_supremum
    (values : q258374_ennreal -> Prop)
    (bound : q258374_ennreal) : Prop :=
  (forall value : q258374_ennreal,
      values value -> q258374_ennreal_le value bound) /\
  (forall upper : q258374_ennreal,
      (forall value : q258374_ennreal,
        values value -> q258374_ennreal_le value upper) ->
      q258374_ennreal_le bound upper).

Definition q258374_ennreal_series_sum
    (u : nat -> q258374_ennreal)
    (sum : q258374_ennreal) : Prop :=
  q258374_ennreal_supremum
    (fun value =>
      exists n : nat,
        q258374_ennreal_eq value
          (q258374_ennreal_partial_sum u n))
    sum.

Record q258374_outer_measure (A : Type) : Type := {
  q258374_outer_measure_value :
    q258374_set A -> q258374_ennreal;
  q258374_outer_measure_extensional :
    forall E F : q258374_set A,
      q258374_same_set E F ->
      q258374_ennreal_eq
        (q258374_outer_measure_value E)
        (q258374_outer_measure_value F);
  q258374_outer_measure_empty :
    q258374_ennreal_eq
      (q258374_outer_measure_value q258374_empty)
      q258374_ennreal_zero;
  q258374_outer_measure_monotone :
    forall E F : q258374_set A,
      q258374_subset E F ->
      q258374_ennreal_le
        (q258374_outer_measure_value E)
        (q258374_outer_measure_value F);
  q258374_outer_measure_countably_subadditive :
    forall E : nat -> q258374_set A,
      exists total : q258374_ennreal,
        q258374_ennreal_series_sum
          (fun n => q258374_outer_measure_value (E n)) total /\
        q258374_ennreal_le
          (q258374_outer_measure_value
            (q258374_countable_union E))
          total
}.

Arguments q258374_outer_measure_value {A} _ _.

Record q258374_measurable_space (A : Type) : Type := {
  q258374_measurable : q258374_set A -> Prop;
  q258374_measurable_extensional :
    forall E F : q258374_set A,
      q258374_same_set E F ->
      (q258374_measurable E <-> q258374_measurable F);
  q258374_measurable_empty :
    q258374_measurable q258374_empty;
  q258374_measurable_complement :
    forall E : q258374_set A,
      q258374_measurable E ->
      q258374_measurable (q258374_complement E);
  q258374_measurable_countable_union :
    forall E : nat -> q258374_set A,
      (forall n : nat, q258374_measurable (E n)) ->
      q258374_measurable (q258374_countable_union E)
}.

Arguments q258374_measurable {A} _ _.

Definition q258374_is_caratheodory {A : Type}
    (mu : q258374_outer_measure A)
    (S : q258374_set A) : Prop :=
  forall T : q258374_set A,
    q258374_ennreal_eq
      (q258374_outer_measure_value mu T)
      (q258374_ennreal_add
        (q258374_outer_measure_value mu
          (q258374_intersection T S))
        (q258374_outer_measure_value mu
          (q258374_difference T S))).

Theorem MeasureTheory_OuterMeasure_caratheodory :
  forall (Alpha : Type) (mu : q258374_outer_measure Alpha),
    exists M : q258374_measurable_space Alpha,
      forall S : q258374_set Alpha,
        q258374_measurable M S <->
        q258374_is_caratheodory mu S.
Admitted.
