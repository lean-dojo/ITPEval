(*
  Statement-only formalization of Thousand Theorems corpus artifact Q842953
  (thousand-theorems__rocq__Q842953), "Lebesgue's density theorem": in a
  second-countable metric space with the Besicovitch covering property, almost
  every point of an arbitrary set, relative to a locally finite Borel measure
  restricted to that set, has density one in shrinking closed balls. This file
  contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q842953_set (A : Type) : Type := A -> Prop.

Definition q842953_empty {A : Type} : q842953_set A :=
  fun _ => False.

Definition q842953_complement {A : Type}
    (E : q842953_set A) : q842953_set A :=
  fun x => ~ E x.

Definition q842953_intersection {A : Type}
    (E F : q842953_set A) : q842953_set A :=
  fun x => E x /\ F x.

Definition q842953_countable_union {A : Type}
    (E : nat -> q842953_set A) : q842953_set A :=
  fun x => exists n : nat, E n x.

Definition q842953_same_set {A : Type}
    (E F : q842953_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q842953_subset {A : Type}
    (E F : q842953_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q842953_disjoint {A : Type}
    (E F : q842953_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q842953_pairwise_disjoint {A : Type}
    (E : nat -> q842953_set A) : Prop :=
  forall i j : nat, i <> j -> q842953_disjoint (E i) (E j).

Inductive q842953_ennreal : Type :=
| q842953_ennreal_finite :
    forall value : R, 0 <= value -> q842953_ennreal
| q842953_ennreal_infinity : q842953_ennreal.

Arguments q842953_ennreal_finite value nonnegative : clear implicits.

Definition q842953_ennreal_zero : q842953_ennreal :=
  q842953_ennreal_finite 0 (Rle_refl 0).

Definition q842953_ennreal_eq
    (x y : q842953_ennreal) : Prop :=
  match x, y with
  | q842953_ennreal_finite a _,
    q842953_ennreal_finite b _ => a = b
  | q842953_ennreal_infinity,
    q842953_ennreal_infinity => True
  | _, _ => False
  end.

Definition q842953_ennreal_le
    (x y : q842953_ennreal) : Prop :=
  match x, y with
  | q842953_ennreal_finite a _,
    q842953_ennreal_finite b _ => a <= b
  | q842953_ennreal_finite _ _,
    q842953_ennreal_infinity => True
  | q842953_ennreal_infinity,
    q842953_ennreal_finite _ _ => False
  | q842953_ennreal_infinity,
    q842953_ennreal_infinity => True
  end.

Definition q842953_ennreal_add
    (x y : q842953_ennreal) : q842953_ennreal :=
  match x, y with
  | q842953_ennreal_finite a ha,
    q842953_ennreal_finite b hb =>
      q842953_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q842953_ennreal_infinity
  end.

Fixpoint q842953_ennreal_partial_sum
    (u : nat -> q842953_ennreal)
    (n : nat) : q842953_ennreal :=
  match n with
  | O => q842953_ennreal_zero
  | S k =>
      q842953_ennreal_add
        (q842953_ennreal_partial_sum u k) (u k)
  end.

Definition q842953_ennreal_supremum
    (values : q842953_ennreal -> Prop)
    (bound : q842953_ennreal) : Prop :=
  (forall value : q842953_ennreal,
      values value -> q842953_ennreal_le value bound) /\
  (forall upper : q842953_ennreal,
      (forall value : q842953_ennreal,
        values value -> q842953_ennreal_le value upper) ->
      q842953_ennreal_le bound upper).

Definition q842953_ennreal_series_sum
    (u : nat -> q842953_ennreal)
    (sum : q842953_ennreal) : Prop :=
  q842953_ennreal_supremum
    (fun value =>
      exists n : nat,
        q842953_ennreal_eq value
          (q842953_ennreal_partial_sum u n))
    sum.

Definition q842953_ennreal_is_finite
    (x : q842953_ennreal) : Prop :=
  exists (value : R) (nonnegative : 0 <= value),
    q842953_ennreal_eq x
      (q842953_ennreal_finite value nonnegative).

Definition q842953_ennreal_div_value
    (numerator denominator : q842953_ennreal) : option R :=
  match numerator, denominator with
  | q842953_ennreal_finite a _,
    q842953_ennreal_finite b _ =>
      if Req_EM_T b 0 then
        if Req_EM_T a 0 then Some 0 else None
      else Some (a / b)
  | q842953_ennreal_finite _ _,
    q842953_ennreal_infinity => Some 0
  | q842953_ennreal_infinity,
    q842953_ennreal_finite _ _ => None
  | q842953_ennreal_infinity,
    q842953_ennreal_infinity => Some 0
  end.

Record q842953_metric_space (A : Type) : Type := {
  q842953_dist : A -> A -> R;
  q842953_dist_nonnegative :
    forall x y : A, 0 <= q842953_dist x y;
  q842953_dist_eq_zero :
    forall x y : A, q842953_dist x y = 0 <-> x = y;
  q842953_dist_symmetric :
    forall x y : A, q842953_dist x y = q842953_dist y x;
  q842953_dist_triangle :
    forall x y z : A,
      q842953_dist x z <= q842953_dist x y + q842953_dist y z
}.

Arguments q842953_dist {A} _ _ _.

Definition q842953_open_ball {A : Type}
    (M : q842953_metric_space A)
    (center : A) (radius : R) : q842953_set A :=
  fun x => q842953_dist M x center < radius.

Definition q842953_closed_ball {A : Type}
    (M : q842953_metric_space A)
    (center : A) (radius : R) : q842953_set A :=
  fun x => q842953_dist M x center <= radius.

Definition q842953_open {A : Type}
    (M : q842953_metric_space A)
    (U : q842953_set A) : Prop :=
  forall x : A,
    U x ->
    exists radius : R,
      0 < radius /\
      q842953_subset (q842953_open_ball M x radius) U.

Definition q842953_sigma_class {A : Type}
    (C : q842953_set (q842953_set A)) : Prop :=
  C q842953_empty /\
  (forall E F : q842953_set A,
    q842953_same_set E F ->
    C E ->
    C F) /\
  (forall E : q842953_set A,
    C E -> C (q842953_complement E)) /\
  (forall E : nat -> q842953_set A,
    (forall n : nat, C (E n)) ->
    C (q842953_countable_union E)).

Definition q842953_borel_set {A : Type}
    (M : q842953_metric_space A)
    (E : q842953_set A) : Prop :=
  forall C : q842953_set (q842953_set A),
    q842953_sigma_class C ->
    (forall U : q842953_set A, q842953_open M U -> C U) ->
    C E.

Record q842953_measurable_space (A : Type) : Type := {
  q842953_measurable : q842953_set A -> Prop;
  q842953_measurable_extensional :
    forall E F : q842953_set A,
      q842953_same_set E F ->
      (q842953_measurable E <-> q842953_measurable F);
  q842953_measurable_empty :
    q842953_measurable q842953_empty;
  q842953_measurable_complement :
    forall E : q842953_set A,
      q842953_measurable E ->
      q842953_measurable (q842953_complement E);
  q842953_measurable_countable_union :
    forall E : nat -> q842953_set A,
      (forall n : nat, q842953_measurable (E n)) ->
      q842953_measurable (q842953_countable_union E)
}.

Arguments q842953_measurable {A} _ _.

Definition q842953_borel_space {A : Type}
    (M : q842953_metric_space A)
    (m : q842953_measurable_space A) : Prop :=
  forall E : q842953_set A,
    q842953_measurable m E <-> q842953_borel_set M E.

Definition q842953_second_countable {A : Type}
    (M : q842953_metric_space A) : Prop :=
  exists basis : nat -> q842953_set A,
    (forall n : nat, q842953_open M (basis n)) /\
    forall (U : q842953_set A) (x : A),
      q842953_open M U ->
      U x ->
      exists n : nat,
        basis n x /\ q842953_subset (basis n) U.

Record q842953_measure (A : Type)
    (m : q842953_measurable_space A) : Type := {
  q842953_measure_value : q842953_set A -> q842953_ennreal;
  q842953_measure_extensional :
    forall E F : q842953_set A,
      q842953_same_set E F ->
      q842953_ennreal_eq
        (q842953_measure_value E)
        (q842953_measure_value F);
  q842953_measure_empty :
    q842953_ennreal_eq
      (q842953_measure_value q842953_empty)
      q842953_ennreal_zero;
  q842953_measure_monotone :
    forall E F : q842953_set A,
      q842953_subset E F ->
      q842953_ennreal_le
        (q842953_measure_value E)
        (q842953_measure_value F);
  q842953_measure_trim :
    forall E : q842953_set A,
      exists F : q842953_set A,
        q842953_measurable m F /\
        q842953_subset E F /\
        q842953_ennreal_eq
          (q842953_measure_value F)
          (q842953_measure_value E);
  q842953_measure_countable_additive :
    forall E : nat -> q842953_set A,
      (forall n : nat, q842953_measurable m (E n)) ->
      q842953_pairwise_disjoint E ->
      q842953_ennreal_series_sum
        (fun n => q842953_measure_value (E n))
        (q842953_measure_value (q842953_countable_union E))
}.

Arguments q842953_measure_value {A m} _ _.

Definition q842953_locally_finite {A : Type}
    {m : q842953_measurable_space A}
    (M : q842953_metric_space A)
    (mu : q842953_measure m) : Prop :=
  forall x : A,
    exists radius : R,
      0 < radius /\
      q842953_ennreal_is_finite
        (q842953_measure_value mu
          (q842953_open_ball M x radius)).

Definition q842953_satellite_configuration {A : Type}
    (M : q842953_metric_space A)
    (N : nat) (tau : R) : Prop :=
  exists (centers : nat -> A) (radii : nat -> R),
    (forall i : nat,
      (i <= N)%nat -> 0 < radii i) /\
    (forall i j : nat,
      (i <= N)%nat ->
      (j <= N)%nat ->
      i <> j ->
      ((radii i <= q842953_dist M (centers i) (centers j) /\
        radii j <= tau * radii i) \/
       (radii j <= q842953_dist M (centers j) (centers i) /\
        radii i <= tau * radii j))) /\
    (forall i : nat,
      (i < N)%nat ->
      radii i <= q842953_dist M (centers i) (centers N) /\
      radii N <= tau * radii i) /\
    forall i : nat,
      (i < N)%nat ->
      q842953_dist M (centers i) (centers N) <=
      radii i + radii N.

Definition q842953_has_besicovitch_covering {A : Type}
    (M : q842953_metric_space A) : Prop :=
  exists (N : nat) (tau : R),
    1 < tau /\
    ~ q842953_satellite_configuration M N tau.

Definition q842953_almost_everywhere_restrict {A : Type}
    {m : q842953_measurable_space A}
    (mu : q842953_measure m)
    (s : q842953_set A)
    (P : A -> Prop) : Prop :=
  exists null_set : q842953_set A,
    q842953_measurable m null_set /\
    q842953_ennreal_eq
      (q842953_measure_value mu
        (q842953_intersection null_set s))
      q842953_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Definition q842953_density_tends_to_one {A : Type}
    {m : q842953_measurable_space A}
    (M : q842953_metric_space A)
    (mu : q842953_measure m)
    (s : q842953_set A)
    (x : A) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall radius : R,
        0 < radius ->
        radius < delta ->
        match
          q842953_ennreal_div_value
            (q842953_measure_value mu
              (q842953_intersection s
                (q842953_closed_ball M x radius)))
            (q842953_measure_value mu
              (q842953_closed_ball M x radius))
        with
        | Some quotient => Rabs (quotient - 1) < epsilon
        | None => False
        end.

Theorem Besicovitch_ae_tendsto_measure_inter_div :
  forall (Beta : Type)
         (M : q842953_metric_space Beta)
         (m : q842953_measurable_space Beta)
         (mu : q842953_measure m)
         (s : q842953_set Beta),
    q842953_borel_space M m ->
    q842953_second_countable M ->
    q842953_has_besicovitch_covering M ->
    q842953_locally_finite M mu ->
    q842953_almost_everywhere_restrict mu s
      (q842953_density_tends_to_one M mu s).
Admitted.
