(*
  Statement-only formalization of Thousand Theorems corpus artifact Q137164
  (thousand-theorems__rocq__Q137164), "Besicovitch covering theorem":
  in a second-countable metric space with the Besicovitch covering property,
  arbitrarily small admissible radii yield a countable pairwise-disjoint
  family of closed balls covering a set almost everywhere for any s-finite
  measure. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q137164_set (A : Type) : Type := A -> Prop.

Definition q137164_empty {A : Type} : q137164_set A :=
  fun _ => False.

Definition q137164_full {A : Type} : q137164_set A :=
  fun _ => True.

Definition q137164_complement {A : Type}
    (E : q137164_set A) : q137164_set A :=
  fun x => ~ E x.

Definition q137164_intersection {A : Type}
    (E F : q137164_set A) : q137164_set A :=
  fun x => E x /\ F x.

Definition q137164_difference {A : Type}
    (E F : q137164_set A) : q137164_set A :=
  fun x => E x /\ ~ F x.

Definition q137164_countable_union {A : Type}
    (E : nat -> q137164_set A) : q137164_set A :=
  fun x => exists n : nat, E n x.

Definition q137164_same_set {A : Type}
    (E F : q137164_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q137164_subset {A : Type}
    (E F : q137164_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q137164_disjoint {A : Type}
    (E F : q137164_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q137164_pairwise_disjoint_sequence {A : Type}
    (E : nat -> q137164_set A) : Prop :=
  forall i j : nat,
    i <> j -> q137164_disjoint (E i) (E j).

Definition q137164_countable {A : Type}
    (E : q137164_set A) : Prop :=
  exists code : A -> nat,
    forall x y : A,
      E x ->
      E y ->
      code x = code y ->
      x = y.

Record q137164_metric_space (A : Type) : Type := {
  q137164_dist : A -> A -> R;
  q137164_dist_nonnegative :
    forall x y : A, 0 <= q137164_dist x y;
  q137164_dist_eq_zero :
    forall x y : A, q137164_dist x y = 0 <-> x = y;
  q137164_dist_symmetric :
    forall x y : A, q137164_dist x y = q137164_dist y x;
  q137164_dist_triangle :
    forall x y z : A,
      q137164_dist x z <= q137164_dist x y + q137164_dist y z
}.

Arguments q137164_dist {A} _ _ _.

Definition q137164_open {A : Type}
    (M : q137164_metric_space A)
    (U : q137164_set A) : Prop :=
  forall x : A,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : A,
        q137164_dist M y x < epsilon ->
        U y.

Definition q137164_second_countable {A : Type}
    (M : q137164_metric_space A) : Prop :=
  exists basis : nat -> q137164_set A,
    (forall n : nat, q137164_open M (basis n)) /\
    forall (U : q137164_set A) (x : A),
      q137164_open M U ->
      U x ->
      exists n : nat,
        basis n x /\ q137164_subset (basis n) U.

Definition q137164_closed_ball {A : Type}
    (M : q137164_metric_space A)
    (center : A) (radius : R) : q137164_set A :=
  fun x => q137164_dist M x center <= radius.

Definition q137164_pairwise_disjoint_balls {A : Type}
    (M : q137164_metric_space A)
    (centers : q137164_set A)
    (radius : A -> R) : Prop :=
  forall x y : A,
    centers x ->
    centers y ->
    x <> y ->
    q137164_disjoint
      (q137164_closed_ball M x (radius x))
      (q137164_closed_ball M y (radius y)).

Definition q137164_union_balls {A : Type}
    (M : q137164_metric_space A)
    (centers : q137164_set A)
    (radius : A -> R) : q137164_set A :=
  fun y =>
    exists x : A,
      centers x /\ q137164_closed_ball M x (radius x) y.

Definition q137164_satellite_config {A : Type}
    (M : q137164_metric_space A)
    (N : nat) (tau : R) : Prop :=
  exists (center : nat -> A) (radius : nat -> R),
    (forall i : nat,
      (i < S N)%nat ->
      0 < radius i) /\
    (forall i j : nat,
      (i < S N)%nat ->
      (j < S N)%nat ->
      i <> j ->
      ((radius i <= q137164_dist M (center i) (center j) /\
        radius j <= tau * radius i) \/
       (radius j <= q137164_dist M (center j) (center i) /\
        radius i <= tau * radius j))) /\
    (forall i : nat,
      (i < N)%nat ->
      radius i <= q137164_dist M (center i) (center N) /\
      radius N <= tau * radius i) /\
    (forall i : nat,
      (i < N)%nat ->
      q137164_dist M (center i) (center N) <=
        radius i + radius N).

Definition q137164_has_besicovitch_covering {A : Type}
    (M : q137164_metric_space A) : Prop :=
  exists (N : nat) (tau : R),
    1 < tau /\ ~ q137164_satellite_config M N tau.

Inductive q137164_ennreal : Type :=
| q137164_ennreal_finite :
    forall value : R, 0 <= value -> q137164_ennreal
| q137164_ennreal_infinity : q137164_ennreal.

Arguments q137164_ennreal_finite value nonnegative : clear implicits.

Definition q137164_ennreal_zero : q137164_ennreal :=
  q137164_ennreal_finite 0 (Rle_refl 0).

Definition q137164_ennreal_eq
    (x y : q137164_ennreal) : Prop :=
  match x, y with
  | q137164_ennreal_finite a _,
    q137164_ennreal_finite b _ => a = b
  | q137164_ennreal_infinity,
    q137164_ennreal_infinity => True
  | _, _ => False
  end.

Definition q137164_ennreal_le
    (x y : q137164_ennreal) : Prop :=
  match x, y with
  | q137164_ennreal_finite a _,
    q137164_ennreal_finite b _ => a <= b
  | q137164_ennreal_finite _ _,
    q137164_ennreal_infinity => True
  | q137164_ennreal_infinity,
    q137164_ennreal_finite _ _ => False
  | q137164_ennreal_infinity,
    q137164_ennreal_infinity => True
  end.

Definition q137164_ennreal_lt
    (x y : q137164_ennreal) : Prop :=
  match x, y with
  | q137164_ennreal_finite a _,
    q137164_ennreal_finite b _ => a < b
  | q137164_ennreal_finite _ _,
    q137164_ennreal_infinity => True
  | _, _ => False
  end.

Definition q137164_ennreal_add
    (x y : q137164_ennreal) : q137164_ennreal :=
  match x, y with
  | q137164_ennreal_finite a ha,
    q137164_ennreal_finite b hb =>
      q137164_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q137164_ennreal_infinity
  end.

Fixpoint q137164_ennreal_partial_sum
    (u : nat -> q137164_ennreal)
    (n : nat) : q137164_ennreal :=
  match n with
  | O => q137164_ennreal_zero
  | S k =>
      q137164_ennreal_add
        (q137164_ennreal_partial_sum u k) (u k)
  end.

Definition q137164_ennreal_series_sum
    (u : nat -> q137164_ennreal)
    (total : q137164_ennreal) : Prop :=
  (forall n : nat,
    q137164_ennreal_le
      (q137164_ennreal_partial_sum u n) total) /\
  forall upper : q137164_ennreal,
    (forall n : nat,
      q137164_ennreal_le
        (q137164_ennreal_partial_sum u n) upper) ->
    q137164_ennreal_le total upper.

Record q137164_measurable_space (A : Type) : Type := {
  q137164_measurable : q137164_set A -> Prop;
  q137164_measurable_extensional :
    forall E F : q137164_set A,
      q137164_same_set E F ->
      (q137164_measurable E <-> q137164_measurable F);
  q137164_measurable_empty :
    q137164_measurable q137164_empty;
  q137164_measurable_complement :
    forall E : q137164_set A,
      q137164_measurable E ->
      q137164_measurable (q137164_complement E);
  q137164_measurable_countable_union :
    forall E : nat -> q137164_set A,
      (forall n : nat, q137164_measurable (E n)) ->
      q137164_measurable (q137164_countable_union E)
}.

Arguments q137164_measurable {A} _ _.

Definition q137164_opens_measurable {A : Type}
    (M : q137164_metric_space A)
    (m : q137164_measurable_space A) : Prop :=
  forall U : q137164_set A,
    q137164_open M U -> q137164_measurable m U.

Record q137164_measure {A : Type}
    (m : q137164_measurable_space A) : Type := {
  q137164_measure_value : q137164_set A -> q137164_ennreal;
  q137164_measure_extensional :
    forall E F : q137164_set A,
      q137164_same_set E F ->
      q137164_ennreal_eq
        (q137164_measure_value E)
        (q137164_measure_value F);
  q137164_measure_empty :
    q137164_ennreal_eq
      (q137164_measure_value q137164_empty)
      q137164_ennreal_zero;
  q137164_measure_monotone :
    forall E F : q137164_set A,
      q137164_subset E F ->
      q137164_ennreal_le
        (q137164_measure_value E)
        (q137164_measure_value F);
  q137164_measure_trim :
    forall E : q137164_set A,
      exists F : q137164_set A,
        q137164_measurable m F /\
        q137164_subset E F /\
        q137164_ennreal_eq
          (q137164_measure_value F)
          (q137164_measure_value E);
  q137164_measure_countable_subadditive :
    forall E : nat -> q137164_set A,
      exists total : q137164_ennreal,
        q137164_ennreal_series_sum
          (fun n => q137164_measure_value (E n)) total /\
        q137164_ennreal_le
          (q137164_measure_value (q137164_countable_union E))
          total;
  q137164_measure_countable_additive :
    forall E : nat -> q137164_set A,
      (forall n : nat, q137164_measurable m (E n)) ->
      q137164_pairwise_disjoint_sequence E ->
      q137164_ennreal_series_sum
        (fun n => q137164_measure_value (E n))
        (q137164_measure_value (q137164_countable_union E));
  q137164_measure_caratheodory :
    forall E S : q137164_set A,
      q137164_measurable m E ->
      q137164_ennreal_eq
        (q137164_measure_value S)
        (q137164_ennreal_add
          (q137164_measure_value (q137164_intersection S E))
          (q137164_measure_value (q137164_difference S E)))
}.

Arguments q137164_measure_value {A m} _ _.

Definition q137164_s_finite {A : Type}
    {m : q137164_measurable_space A}
    (mu : q137164_measure m) : Prop :=
  exists pieces : nat -> q137164_measure m,
    (forall n : nat,
      q137164_ennreal_lt
        (q137164_measure_value (pieces n) q137164_full)
        q137164_ennreal_infinity) /\
    forall E : q137164_set A,
      exists total : q137164_ennreal,
        q137164_ennreal_series_sum
          (fun n => q137164_measure_value (pieces n) E)
          total /\
        q137164_ennreal_eq
          (q137164_measure_value mu E) total.

Theorem exists_disjoint_closedBall_covering_ae :
  forall (Alpha : Type)
         (M : q137164_metric_space Alpha)
         (m : q137164_measurable_space Alpha)
         (mu : q137164_measure m)
         (f : Alpha -> q137164_set R)
         (s : q137164_set Alpha)
         (Rbound : Alpha -> R),
    q137164_second_countable M ->
    q137164_opens_measurable M m ->
    q137164_s_finite mu ->
    q137164_has_besicovitch_covering M ->
    (forall (x : Alpha) (delta : R),
      s x ->
      0 < delta ->
      exists radius : R,
        f x radius /\ 0 < radius /\ radius < delta) ->
    (forall x : Alpha, s x -> 0 < Rbound x) ->
    exists (t : q137164_set Alpha) (radius : Alpha -> R),
      q137164_countable t /\
      q137164_subset t s /\
      (forall x : Alpha,
        t x ->
        f x (radius x) /\
        0 < radius x /\
        radius x < Rbound x) /\
      q137164_ennreal_eq
        (q137164_measure_value mu
          (q137164_difference s
            (q137164_union_balls M t radius)))
        q137164_ennreal_zero /\
      q137164_pairwise_disjoint_balls M t radius.
Admitted.
