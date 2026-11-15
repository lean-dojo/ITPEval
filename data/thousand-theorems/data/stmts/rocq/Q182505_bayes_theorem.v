(*
  Statement-only formalization of Thousand Theorems corpus artifact Q182505
  (thousand-theorems__rocq__Q182505), "Bayes' theorem": for two measurable
  events in a finite measure space, conditional probability in one direction
  equals the inverse measure of the conditioning event times the reverse
  conditional probability times the other event's measure. This file contains
  no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q182505_set (A : Type) : Type := A -> Prop.

Definition q182505_empty {A : Type} : q182505_set A :=
  fun _ => False.

Definition q182505_full {A : Type} : q182505_set A :=
  fun _ => True.

Definition q182505_complement {A : Type}
    (E : q182505_set A) : q182505_set A :=
  fun x => ~ E x.

Definition q182505_intersection {A : Type}
    (E F : q182505_set A) : q182505_set A :=
  fun x => E x /\ F x.

Definition q182505_countable_union {A : Type}
    (E : nat -> q182505_set A) : q182505_set A :=
  fun x => exists n : nat, E n x.

Definition q182505_same_set {A : Type}
    (E F : q182505_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q182505_disjoint {A : Type}
    (E F : q182505_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q182505_pairwise_disjoint {A : Type}
    (E : nat -> q182505_set A) : Prop :=
  forall i j : nat, i <> j -> q182505_disjoint (E i) (E j).

Inductive q182505_ennreal : Type :=
| q182505_ennreal_finite :
    forall value : R, 0 <= value -> q182505_ennreal
| q182505_ennreal_infinity : q182505_ennreal.

Arguments q182505_ennreal_finite value nonnegative : clear implicits.

Definition q182505_ennreal_zero : q182505_ennreal :=
  q182505_ennreal_finite 0 (Rle_refl 0).

Definition q182505_ennreal_eq
    (x y : q182505_ennreal) : Prop :=
  match x, y with
  | q182505_ennreal_finite a _,
    q182505_ennreal_finite b _ => a = b
  | q182505_ennreal_infinity,
    q182505_ennreal_infinity => True
  | _, _ => False
  end.

Definition q182505_ennreal_le
    (x y : q182505_ennreal) : Prop :=
  match x, y with
  | q182505_ennreal_finite a _,
    q182505_ennreal_finite b _ => a <= b
  | q182505_ennreal_finite _ _,
    q182505_ennreal_infinity => True
  | q182505_ennreal_infinity,
    q182505_ennreal_finite _ _ => False
  | q182505_ennreal_infinity,
    q182505_ennreal_infinity => True
  end.

Definition q182505_ennreal_add
    (x y : q182505_ennreal) : q182505_ennreal :=
  match x, y with
  | q182505_ennreal_finite a ha,
    q182505_ennreal_finite b hb =>
      q182505_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q182505_ennreal_infinity
  end.

Definition q182505_ennreal_mul
    (x y : q182505_ennreal) : q182505_ennreal :=
  match x, y with
  | q182505_ennreal_finite a ha,
    q182505_ennreal_finite b hb =>
      q182505_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q182505_ennreal_finite a _, q182505_ennreal_infinity
  | q182505_ennreal_infinity, q182505_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q182505_ennreal_zero
      else q182505_ennreal_infinity
  | q182505_ennreal_infinity, q182505_ennreal_infinity =>
      q182505_ennreal_infinity
  end.

Definition q182505_ennreal_inv
    (x : q182505_ennreal) : q182505_ennreal :=
  match x with
  | q182505_ennreal_finite a ha =>
      match Rle_lt_or_eq_dec 0 a ha with
      | left hpositive =>
          q182505_ennreal_finite
            (/ a)
            (Rlt_le 0 (/ a) (Rinv_0_lt_compat a hpositive))
      | right _ => q182505_ennreal_infinity
      end
  | q182505_ennreal_infinity => q182505_ennreal_zero
  end.

Fixpoint q182505_ennreal_partial_sum
    (u : nat -> q182505_ennreal)
    (n : nat) : q182505_ennreal :=
  match n with
  | O => q182505_ennreal_zero
  | S k =>
      q182505_ennreal_add
        (q182505_ennreal_partial_sum u k) (u k)
  end.

Definition q182505_ennreal_supremum
    (values : q182505_ennreal -> Prop)
    (bound : q182505_ennreal) : Prop :=
  (forall value : q182505_ennreal,
      values value -> q182505_ennreal_le value bound) /\
  (forall upper : q182505_ennreal,
      (forall value : q182505_ennreal,
        values value -> q182505_ennreal_le value upper) ->
      q182505_ennreal_le bound upper).

Definition q182505_ennreal_series_sum
    (u : nat -> q182505_ennreal)
    (sum : q182505_ennreal) : Prop :=
  q182505_ennreal_supremum
    (fun value =>
      exists n : nat,
        q182505_ennreal_eq value
          (q182505_ennreal_partial_sum u n))
    sum.

Definition q182505_ennreal_represents
    (x : q182505_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q182505_ennreal_eq x
      (q182505_ennreal_finite value nonnegative).

Definition q182505_ennreal_finite_value
    (x : q182505_ennreal) : Prop :=
  exists value : R, q182505_ennreal_represents x value.

Record q182505_measurable_space (A : Type) : Type := {
  q182505_measurable : q182505_set A -> Prop;
  q182505_measurable_extensional :
    forall E F : q182505_set A,
      q182505_same_set E F ->
      (q182505_measurable E <-> q182505_measurable F);
  q182505_measurable_empty :
    q182505_measurable q182505_empty;
  q182505_measurable_complement :
    forall E : q182505_set A,
      q182505_measurable E ->
      q182505_measurable (q182505_complement E);
  q182505_measurable_countable_union :
    forall E : nat -> q182505_set A,
      (forall n : nat, q182505_measurable (E n)) ->
      q182505_measurable (q182505_countable_union E)
}.

Arguments q182505_measurable {A} _ _.

Record q182505_measure {A : Type}
    (M : q182505_measurable_space A) : Type := {
  q182505_measure_value :
    q182505_set A -> q182505_ennreal;
  q182505_measure_extensional :
    forall E F : q182505_set A,
      q182505_same_set E F ->
      q182505_ennreal_eq
        (q182505_measure_value E)
        (q182505_measure_value F);
  q182505_measure_empty :
    q182505_ennreal_eq
      (q182505_measure_value q182505_empty)
      q182505_ennreal_zero;
  q182505_measure_countable_additive :
    forall E : nat -> q182505_set A,
      (forall n : nat, q182505_measurable M (E n)) ->
      q182505_pairwise_disjoint E ->
      q182505_ennreal_series_sum
        (fun n => q182505_measure_value (E n))
        (q182505_measure_value (q182505_countable_union E))
}.

Arguments q182505_measure_value {A M} _ _.

Definition q182505_finite_measure {A : Type}
    {M : q182505_measurable_space A}
    (mu : q182505_measure M) : Prop :=
  q182505_ennreal_finite_value
    (q182505_measure_value mu q182505_full).

Definition q182505_conditional_probability {A : Type}
    {M : q182505_measurable_space A}
    (mu : q182505_measure M)
    (event given : q182505_set A) : q182505_ennreal :=
  q182505_ennreal_mul
    (q182505_ennreal_inv (q182505_measure_value mu given))
    (q182505_measure_value mu
      (q182505_intersection given event)).

Theorem cond_eq_inv_mul_cond_mul :
  forall (Omega : Type)
         (M : q182505_measurable_space Omega)
         (mu : q182505_measure M)
         (s t : q182505_set Omega),
    q182505_measurable M s ->
    q182505_measurable M t ->
    q182505_finite_measure mu ->
    q182505_ennreal_eq
      (q182505_conditional_probability mu t s)
      (q182505_ennreal_mul
        (q182505_ennreal_mul
          (q182505_ennreal_inv (q182505_measure_value mu s))
          (q182505_conditional_probability mu s t))
        (q182505_measure_value mu t)).
Admitted.
