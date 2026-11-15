(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5437947
  (thousand-theorems__rocq__Q5437947), "Fatou–Lebesgue theorem":
  Fatou's inequality for a sequence of measurable extended-nonnegative
  functions on an arbitrary measure space. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q5437947_set (A : Type) : Type := A -> Prop.

Definition q5437947_empty {A : Type} : q5437947_set A :=
  fun _ => False.

Definition q5437947_complement {A : Type}
    (E : q5437947_set A) : q5437947_set A :=
  fun x => ~ E x.

Definition q5437947_countable_union {A : Type}
    (E : nat -> q5437947_set A) : q5437947_set A :=
  fun x => exists n : nat, E n x.

Definition q5437947_same_set {A : Type}
    (E F : q5437947_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q5437947_disjoint {A : Type}
    (E F : q5437947_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q5437947_pairwise_disjoint {A : Type}
    (E : nat -> q5437947_set A) : Prop :=
  forall i j : nat, i <> j -> q5437947_disjoint (E i) (E j).

Inductive q5437947_ennreal : Type :=
| q5437947_ennreal_finite :
    forall value : R, 0 <= value -> q5437947_ennreal
| q5437947_ennreal_infinity : q5437947_ennreal.

Arguments q5437947_ennreal_finite value nonnegative : clear implicits.

Definition q5437947_ennreal_zero : q5437947_ennreal :=
  q5437947_ennreal_finite 0 (Rle_refl 0).

Definition q5437947_ennreal_eq
    (x y : q5437947_ennreal) : Prop :=
  match x, y with
  | q5437947_ennreal_finite a _,
    q5437947_ennreal_finite b _ => a = b
  | q5437947_ennreal_infinity,
    q5437947_ennreal_infinity => True
  | _, _ => False
  end.

Definition q5437947_ennreal_le
    (x y : q5437947_ennreal) : Prop :=
  match x, y with
  | q5437947_ennreal_finite a _,
    q5437947_ennreal_finite b _ => a <= b
  | q5437947_ennreal_finite _ _,
    q5437947_ennreal_infinity => True
  | q5437947_ennreal_infinity,
    q5437947_ennreal_finite _ _ => False
  | q5437947_ennreal_infinity,
    q5437947_ennreal_infinity => True
  end.

Definition q5437947_ennreal_add
    (x y : q5437947_ennreal) : q5437947_ennreal :=
  match x, y with
  | q5437947_ennreal_finite a ha,
    q5437947_ennreal_finite b hb =>
      q5437947_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q5437947_ennreal_infinity
  end.

Definition q5437947_ennreal_mul
    (x y : q5437947_ennreal) : q5437947_ennreal :=
  match x, y with
  | q5437947_ennreal_finite a ha,
    q5437947_ennreal_finite b hb =>
      q5437947_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q5437947_ennreal_finite a _, q5437947_ennreal_infinity
  | q5437947_ennreal_infinity, q5437947_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q5437947_ennreal_zero
      else q5437947_ennreal_infinity
  | q5437947_ennreal_infinity, q5437947_ennreal_infinity =>
      q5437947_ennreal_infinity
  end.

Fixpoint q5437947_ennreal_partial_sum
    (u : nat -> q5437947_ennreal)
    (n : nat) : q5437947_ennreal :=
  match n with
  | O => q5437947_ennreal_zero
  | S k =>
      q5437947_ennreal_add
        (q5437947_ennreal_partial_sum u k) (u k)
  end.

Definition q5437947_ennreal_supremum
    (values : q5437947_ennreal -> Prop)
    (bound : q5437947_ennreal) : Prop :=
  (forall value : q5437947_ennreal,
      values value -> q5437947_ennreal_le value bound) /\
  (forall upper : q5437947_ennreal,
      (forall value : q5437947_ennreal,
        values value -> q5437947_ennreal_le value upper) ->
      q5437947_ennreal_le bound upper).

Definition q5437947_ennreal_infimum
    (values : q5437947_ennreal -> Prop)
    (bound : q5437947_ennreal) : Prop :=
  (forall value : q5437947_ennreal,
      values value -> q5437947_ennreal_le bound value) /\
  (forall lower : q5437947_ennreal,
      (forall value : q5437947_ennreal,
        values value -> q5437947_ennreal_le lower value) ->
      q5437947_ennreal_le lower bound).

Definition q5437947_ennreal_series_sum
    (u : nat -> q5437947_ennreal)
    (sum : q5437947_ennreal) : Prop :=
  q5437947_ennreal_supremum
    (fun value =>
      exists n : nat,
        q5437947_ennreal_eq value
          (q5437947_ennreal_partial_sum u n))
    sum.

Definition q5437947_liminf_has_value
    (u : nat -> q5437947_ennreal)
    (value : q5437947_ennreal) : Prop :=
  exists tail_infima : nat -> q5437947_ennreal,
    (forall n : nat,
      q5437947_ennreal_infimum
        (fun tail_value =>
          exists k : nat,
            (n <= k)%nat /\
            q5437947_ennreal_eq tail_value (u k))
        (tail_infima n)) /\
    q5437947_ennreal_supremum
      (fun tail_value =>
        exists n : nat,
          q5437947_ennreal_eq tail_value (tail_infima n))
      value.

Record q5437947_measure_space (A : Type) : Type := {
  q5437947_measurable : q5437947_set A -> Prop;
  q5437947_measurable_extensional :
    forall E F : q5437947_set A,
      q5437947_same_set E F ->
      (q5437947_measurable E <-> q5437947_measurable F);
  q5437947_measurable_empty :
    q5437947_measurable q5437947_empty;
  q5437947_measurable_complement :
    forall E : q5437947_set A,
      q5437947_measurable E ->
      q5437947_measurable (q5437947_complement E);
  q5437947_measurable_countable_union :
    forall E : nat -> q5437947_set A,
      (forall n : nat, q5437947_measurable (E n)) ->
      q5437947_measurable (q5437947_countable_union E);
  q5437947_measure : q5437947_set A -> q5437947_ennreal;
  q5437947_measure_extensional :
    forall E F : q5437947_set A,
      q5437947_same_set E F ->
      q5437947_ennreal_eq
        (q5437947_measure E) (q5437947_measure F);
  q5437947_measure_empty :
    q5437947_ennreal_eq
      (q5437947_measure q5437947_empty)
      q5437947_ennreal_zero;
  q5437947_measure_countable_additive :
    forall E : nat -> q5437947_set A,
      (forall n : nat, q5437947_measurable (E n)) ->
      q5437947_pairwise_disjoint E ->
      q5437947_ennreal_series_sum
        (fun n => q5437947_measure (E n))
        (q5437947_measure (q5437947_countable_union E))
}.

Arguments q5437947_measurable {A} _ _.
Arguments q5437947_measure {A} _ _.

Definition q5437947_ennreal_below_real
    (x : q5437947_ennreal) (bound : R) : Prop :=
  match x with
  | q5437947_ennreal_finite value _ => value < bound
  | q5437947_ennreal_infinity => False
  end.

Definition q5437947_measurable_ennreal_function {A : Type}
    (mu : q5437947_measure_space A)
    (f : A -> q5437947_ennreal) : Prop :=
  forall bound : R,
    q5437947_measurable mu
      (fun x => q5437947_ennreal_below_real (f x) bound).

Record q5437947_nonnegative_real : Type := {
  q5437947_nnreal_value : R;
  q5437947_nnreal_nonnegative : 0 <= q5437947_nnreal_value
}.

Definition q5437947_ennreal_of_nonnegative
    (x : q5437947_nonnegative_real) : q5437947_ennreal :=
  q5437947_ennreal_finite
    (q5437947_nnreal_value x)
    (q5437947_nnreal_nonnegative x).

Definition q5437947_finite_partition {A : Type}
    (mu : q5437947_measure_space A)
    (k : nat) (cells : nat -> q5437947_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q5437947_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q5437947_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q5437947_simple_lintegral_below {A : Type}
    (mu : q5437947_measure_space A)
    (f : A -> q5437947_ennreal)
    (value : q5437947_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q5437947_nonnegative_real)
         (cells : nat -> q5437947_set A),
    q5437947_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q5437947_ennreal_le
        (q5437947_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q5437947_ennreal_eq value
      (q5437947_ennreal_partial_sum
        (fun i =>
          q5437947_ennreal_mul
            (q5437947_ennreal_of_nonnegative (coefficients i))
            (q5437947_measure mu (cells i)))
        k).

Definition q5437947_lintegral_has_value {A : Type}
    (mu : q5437947_measure_space A)
    (f : A -> q5437947_ennreal)
    (value : q5437947_ennreal) : Prop :=
  q5437947_ennreal_supremum
    (q5437947_simple_lintegral_below mu f) value.

Theorem lintegral_liminf_le :
  forall (Alpha : Type)
         (mu : q5437947_measure_space Alpha)
         (f : nat -> Alpha -> q5437947_ennreal),
    (forall n : nat,
      q5437947_measurable_ennreal_function mu (f n)) ->
    exists (pointwise_liminf : Alpha -> q5437947_ennreal)
           (integrals : nat -> q5437947_ennreal)
           (left_integral right_liminf : q5437947_ennreal),
      (forall x : Alpha,
        q5437947_liminf_has_value
          (fun n => f n x) (pointwise_liminf x)) /\
      (forall n : nat,
        q5437947_lintegral_has_value
          mu (f n) (integrals n)) /\
      q5437947_lintegral_has_value
        mu pointwise_liminf left_integral /\
      q5437947_liminf_has_value integrals right_liminf /\
      q5437947_ennreal_le left_integral right_liminf.
Admitted.
