(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3229352
  (thousand-theorems__rocq__Q3229352), "Vitali covering theorem": a fine
  family of closed sets in a second-countable pseudo-metric measure space,
  satisfying a uniform measure bound on triple-radius closed balls, has a
  countable pairwise-disjoint subfamily covering the given set up to a null
  set. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3229352_set (A : Type) : Type := A -> Prop.

Definition q3229352_empty {A : Type} : q3229352_set A :=
  fun _ => False.

Definition q3229352_complement {A : Type}
    (E : q3229352_set A) : q3229352_set A :=
  fun x => ~ E x.

Definition q3229352_intersection {A : Type}
    (E F : q3229352_set A) : q3229352_set A :=
  fun x => E x /\ F x.

Definition q3229352_difference {A : Type}
    (E F : q3229352_set A) : q3229352_set A :=
  fun x => E x /\ ~ F x.

Definition q3229352_countable_union {A : Type}
    (E : nat -> q3229352_set A) : q3229352_set A :=
  fun x => exists n : nat, E n x.

Definition q3229352_same_set {A : Type}
    (E F : q3229352_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q3229352_subset {A : Type}
    (E F : q3229352_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q3229352_disjoint {A : Type}
    (E F : q3229352_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q3229352_pairwise_disjoint_sequence {A : Type}
    (E : nat -> q3229352_set A) : Prop :=
  forall i j : nat,
    i <> j -> q3229352_disjoint (E i) (E j).

Inductive q3229352_ennreal : Type :=
| q3229352_ennreal_finite :
    forall value : R, 0 <= value -> q3229352_ennreal
| q3229352_ennreal_infinity : q3229352_ennreal.

Arguments q3229352_ennreal_finite value nonnegative : clear implicits.

Definition q3229352_ennreal_zero : q3229352_ennreal :=
  q3229352_ennreal_finite 0 (Rle_refl 0).

Definition q3229352_ennreal_eq
    (x y : q3229352_ennreal) : Prop :=
  match x, y with
  | q3229352_ennreal_finite a _,
    q3229352_ennreal_finite b _ => a = b
  | q3229352_ennreal_infinity,
    q3229352_ennreal_infinity => True
  | _, _ => False
  end.

Definition q3229352_ennreal_le
    (x y : q3229352_ennreal) : Prop :=
  match x, y with
  | q3229352_ennreal_finite a _,
    q3229352_ennreal_finite b _ => a <= b
  | q3229352_ennreal_finite _ _,
    q3229352_ennreal_infinity => True
  | q3229352_ennreal_infinity,
    q3229352_ennreal_finite _ _ => False
  | q3229352_ennreal_infinity,
    q3229352_ennreal_infinity => True
  end.

Definition q3229352_ennreal_add
    (x y : q3229352_ennreal) : q3229352_ennreal :=
  match x, y with
  | q3229352_ennreal_finite a ha,
    q3229352_ennreal_finite b hb =>
      q3229352_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q3229352_ennreal_infinity
  end.

Definition q3229352_ennreal_mul
    (x y : q3229352_ennreal) : q3229352_ennreal :=
  match x, y with
  | q3229352_ennreal_finite a ha,
    q3229352_ennreal_finite b hb =>
      q3229352_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q3229352_ennreal_finite a _, q3229352_ennreal_infinity
  | q3229352_ennreal_infinity, q3229352_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q3229352_ennreal_zero
      else q3229352_ennreal_infinity
  | q3229352_ennreal_infinity, q3229352_ennreal_infinity =>
      q3229352_ennreal_infinity
  end.

Fixpoint q3229352_ennreal_partial_sum
    (u : nat -> q3229352_ennreal)
    (n : nat) : q3229352_ennreal :=
  match n with
  | O => q3229352_ennreal_zero
  | S k =>
      q3229352_ennreal_add
        (q3229352_ennreal_partial_sum u k) (u k)
  end.

Definition q3229352_ennreal_supremum
    (values : q3229352_ennreal -> Prop)
    (bound : q3229352_ennreal) : Prop :=
  (forall value : q3229352_ennreal,
      values value -> q3229352_ennreal_le value bound) /\
  (forall upper : q3229352_ennreal,
      (forall value : q3229352_ennreal,
        values value -> q3229352_ennreal_le value upper) ->
      q3229352_ennreal_le bound upper).

Definition q3229352_ennreal_series_sum
    (u : nat -> q3229352_ennreal)
    (sum : q3229352_ennreal) : Prop :=
  q3229352_ennreal_supremum
    (fun value =>
      exists n : nat,
        q3229352_ennreal_eq value
          (q3229352_ennreal_partial_sum u n))
    sum.

Record q3229352_nnreal : Type := {
  q3229352_nnreal_value : R;
  q3229352_nnreal_nonnegative : 0 <= q3229352_nnreal_value
}.

Definition q3229352_ennreal_of_nnreal
    (x : q3229352_nnreal) : q3229352_ennreal :=
  q3229352_ennreal_finite
    (q3229352_nnreal_value x)
    (q3229352_nnreal_nonnegative x).

Record q3229352_measurable_space (A : Type) : Type := {
  q3229352_measurable : q3229352_set A -> Prop;
  q3229352_measurable_extensional :
    forall E F : q3229352_set A,
      q3229352_same_set E F ->
      (q3229352_measurable E <-> q3229352_measurable F);
  q3229352_measurable_empty :
    q3229352_measurable q3229352_empty;
  q3229352_measurable_complement :
    forall E : q3229352_set A,
      q3229352_measurable E ->
      q3229352_measurable (q3229352_complement E);
  q3229352_measurable_countable_union :
    forall E : nat -> q3229352_set A,
      (forall n : nat, q3229352_measurable (E n)) ->
      q3229352_measurable (q3229352_countable_union E)
}.

Arguments q3229352_measurable {A} _ _.

Record q3229352_measure (A : Type)
    (m : q3229352_measurable_space A) : Type := {
  q3229352_measure_value : q3229352_set A -> q3229352_ennreal;
  q3229352_measure_extensional :
    forall E F : q3229352_set A,
      q3229352_same_set E F ->
      q3229352_ennreal_eq
        (q3229352_measure_value E)
        (q3229352_measure_value F);
  q3229352_measure_empty :
    q3229352_ennreal_eq
      (q3229352_measure_value q3229352_empty)
      q3229352_ennreal_zero;
  q3229352_measure_monotone :
    forall E F : q3229352_set A,
      q3229352_subset E F ->
      q3229352_ennreal_le
        (q3229352_measure_value E)
        (q3229352_measure_value F);
  q3229352_measure_trim :
    forall E : q3229352_set A,
      exists F : q3229352_set A,
        q3229352_measurable m F /\
        q3229352_subset E F /\
        q3229352_ennreal_eq
          (q3229352_measure_value F)
          (q3229352_measure_value E);
  q3229352_measure_countable_subadditive :
    forall E : nat -> q3229352_set A,
      exists total : q3229352_ennreal,
        q3229352_ennreal_series_sum
          (fun n => q3229352_measure_value (E n)) total /\
        q3229352_ennreal_le
          (q3229352_measure_value (q3229352_countable_union E))
          total;
  q3229352_measure_countable_additive :
    forall E : nat -> q3229352_set A,
      (forall n : nat, q3229352_measurable m (E n)) ->
      q3229352_pairwise_disjoint_sequence E ->
      q3229352_ennreal_series_sum
        (fun n => q3229352_measure_value (E n))
        (q3229352_measure_value (q3229352_countable_union E));
  q3229352_measure_caratheodory :
    forall E S : q3229352_set A,
      q3229352_measurable m E ->
      q3229352_ennreal_eq
        (q3229352_measure_value S)
        (q3229352_ennreal_add
          (q3229352_measure_value (q3229352_intersection S E))
          (q3229352_measure_value (q3229352_difference S E)))
}.

Arguments q3229352_measure_value {A m} _ _.

Record q3229352_pseudo_metric_space (A : Type) : Type := {
  q3229352_dist : A -> A -> R;
  q3229352_dist_nonnegative :
    forall x y : A, 0 <= q3229352_dist x y;
  q3229352_dist_self :
    forall x : A, q3229352_dist x x = 0;
  q3229352_dist_comm :
    forall x y : A, q3229352_dist x y = q3229352_dist y x;
  q3229352_dist_triangle :
    forall x y z : A,
      q3229352_dist x z <=
      q3229352_dist x y + q3229352_dist y z
}.

Arguments q3229352_dist {A} _ _ _.

Definition q3229352_open_ball {A : Type}
    (d : q3229352_pseudo_metric_space A)
    (center : A) (radius : R) : q3229352_set A :=
  fun x => q3229352_dist d x center < radius.

Definition q3229352_closed_ball {A : Type}
    (d : q3229352_pseudo_metric_space A)
    (center : A) (radius : R) : q3229352_set A :=
  fun x => q3229352_dist d x center <= radius.

Definition q3229352_is_open {A : Type}
    (d : q3229352_pseudo_metric_space A)
    (E : q3229352_set A) : Prop :=
  forall x : A,
    E x ->
    exists epsilon : R,
      0 < epsilon /\
      q3229352_subset (q3229352_open_ball d x epsilon) E.

Definition q3229352_is_closed {A : Type}
    (d : q3229352_pseudo_metric_space A)
    (E : q3229352_set A) : Prop :=
  q3229352_is_open d (q3229352_complement E).

Definition q3229352_interior {A : Type}
    (d : q3229352_pseudo_metric_space A)
    (E : q3229352_set A) : q3229352_set A :=
  fun x =>
    exists epsilon : R,
      0 < epsilon /\
      q3229352_subset (q3229352_open_ball d x epsilon) E.

Definition q3229352_opens_measurable {A : Type}
    (d : q3229352_pseudo_metric_space A)
    (m : q3229352_measurable_space A) : Prop :=
  forall E : q3229352_set A,
    q3229352_is_open d E ->
    q3229352_measurable m E.

Definition q3229352_second_countable {A : Type}
    (d : q3229352_pseudo_metric_space A) : Prop :=
  exists basis : nat -> q3229352_set A,
    (forall n : nat, q3229352_is_open d (basis n)) /\
    forall (E : q3229352_set A) (x : A),
      q3229352_is_open d E ->
      E x ->
      exists n : nat,
        basis n x /\ q3229352_subset (basis n) E.

Definition q3229352_locally_finite_measure {A : Type}
    {m : q3229352_measurable_space A}
    (d : q3229352_pseudo_metric_space A)
    (mu : q3229352_measure m) : Prop :=
  forall x : A,
    exists E : q3229352_set A,
      q3229352_is_open d E /\
      E x /\
      ~ q3229352_ennreal_eq
          (q3229352_measure_value mu E)
          q3229352_ennreal_infinity.

Definition q3229352_countable_set {A : Type}
    (E : q3229352_set A) : Prop :=
  exists code : A -> nat,
    forall x y : A,
      E x ->
      E y ->
      code x = code y ->
      x = y.

Definition q3229352_pairwise_disjoint_family {I A : Type}
    (u : q3229352_set I)
    (B : I -> q3229352_set A) : Prop :=
  forall a b : I,
    u a ->
    u b ->
    a <> b ->
    q3229352_disjoint (B a) (B b).

Definition q3229352_family_union {I A : Type}
    (u : q3229352_set I)
    (B : I -> q3229352_set A) : q3229352_set A :=
  fun x => exists a : I, u a /\ B a x.

Theorem Vitali_exists_disjoint_covering_ae :
  forall (Alpha Iota : Type)
         (d : q3229352_pseudo_metric_space Alpha)
         (m : q3229352_measurable_space Alpha)
         (mu : q3229352_measure m)
         (s : q3229352_set Alpha)
         (t : q3229352_set Iota)
         (C : q3229352_nnreal)
         (r : Iota -> R)
         (c : Iota -> Alpha)
         (B : Iota -> q3229352_set Alpha),
    q3229352_opens_measurable d m ->
    q3229352_second_countable d ->
    q3229352_locally_finite_measure d mu ->
    (forall a : Iota,
      t a ->
      q3229352_subset
        (B a) (q3229352_closed_ball d (c a) (r a))) ->
    (forall a : Iota,
      t a ->
      q3229352_ennreal_le
        (q3229352_measure_value mu
          (q3229352_closed_ball d (c a) (3 * r a)))
        (q3229352_ennreal_mul
          (q3229352_ennreal_of_nnreal C)
          (q3229352_measure_value mu (B a)))) ->
    (forall a : Iota,
      t a ->
      exists x : Alpha, q3229352_interior d (B a) x) ->
    (forall a : Iota,
      t a ->
      q3229352_is_closed d (B a)) ->
    (forall x : Alpha,
      s x ->
      forall epsilon : R,
        0 < epsilon ->
        exists a : Iota,
          t a /\ r a <= epsilon /\ c a = x) ->
    exists u : q3229352_set Iota,
      q3229352_subset u t /\
      q3229352_countable_set u /\
      q3229352_pairwise_disjoint_family u B /\
      q3229352_ennreal_eq
        (q3229352_measure_value mu
          (q3229352_difference s (q3229352_family_union u B)))
        q3229352_ennreal_zero.
Admitted.
