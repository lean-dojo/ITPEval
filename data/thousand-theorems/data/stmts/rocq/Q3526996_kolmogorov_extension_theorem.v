(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3526996
  (thousand-theorems__rocq__Q3526996), "Kolmogorov extension theorem": every
  projectively consistent family of finite measures on finite products of
  Polish spaces extends to a measure on the full product with the prescribed
  finite-dimensional marginals. This file contains no proof.
*)

From Stdlib Require Import Reals List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3526996_event (A : Type) : Type := A -> Prop.

Definition q3526996_empty {A : Type} : q3526996_event A :=
  fun _ => False.

Definition q3526996_full {A : Type} : q3526996_event A :=
  fun _ => True.

Definition q3526996_complement {A : Type}
    (E : q3526996_event A) : q3526996_event A :=
  fun x => ~ E x.

Definition q3526996_countable_union {A : Type}
    (E : nat -> q3526996_event A) : q3526996_event A :=
  fun x => exists n : nat, E n x.

Definition q3526996_same_event {A : Type}
    (E F : q3526996_event A) : Prop :=
  forall x : A, E x <-> F x.

Definition q3526996_pairwise_disjoint {A : Type}
    (E : nat -> q3526996_event A) : Prop :=
  forall i j : nat, i <> j ->
    forall x : A, ~ (E i x /\ E j x).

Record q3526996_metric_space (A : Type) : Type := {
  q3526996_dist : A -> A -> R;
  q3526996_dist_nonnegative :
    forall x y : A, 0 <= q3526996_dist x y;
  q3526996_dist_eq_zero :
    forall x y : A, q3526996_dist x y = 0 <-> x = y;
  q3526996_dist_symmetric :
    forall x y : A, q3526996_dist x y = q3526996_dist y x;
  q3526996_dist_triangle :
    forall x y z : A,
      q3526996_dist x z <=
      q3526996_dist x y + q3526996_dist y z
}.

Arguments q3526996_dist {A} _ _ _.

Definition q3526996_metric_open {A : Type}
    (d : q3526996_metric_space A)
    (U : q3526996_event A) : Prop :=
  forall x : A, U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : A, q3526996_dist d x y < epsilon -> U y.

Definition q3526996_metric_converges {A : Type}
    (d : q3526996_metric_space A)
    (u : nat -> A) (x : A) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat,
      forall n : nat, (N <= n)%nat ->
        q3526996_dist d (u n) x < epsilon.

Definition q3526996_metric_cauchy {A : Type}
    (d : q3526996_metric_space A)
    (u : nat -> A) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q3526996_dist d (u m) (u n) < epsilon.

Definition q3526996_complete {A : Type}
    (d : q3526996_metric_space A) : Prop :=
  forall u : nat -> A,
    q3526996_metric_cauchy d u ->
    exists x : A, q3526996_metric_converges d u x.

Definition q3526996_second_countable {A : Type}
    (d : q3526996_metric_space A) : Prop :=
  exists basis : nat -> q3526996_event A,
    (forall n : nat, q3526996_metric_open d (basis n)) /\
    forall (U : q3526996_event A) (x : A),
      q3526996_metric_open d U ->
      U x ->
      exists n : nat,
        basis n x /\
        forall y : A, basis n y -> U y.

Record q3526996_polish_space (A : Type) : Type := {
  q3526996_polish_metric : q3526996_metric_space A;
  q3526996_polish_complete :
    q3526996_complete q3526996_polish_metric;
  q3526996_polish_second_countable :
    q3526996_second_countable q3526996_polish_metric
}.

Inductive q3526996_borel {A : Type}
    (S : q3526996_polish_space A)
    : q3526996_event A -> Prop :=
| q3526996_borel_open :
    forall U : q3526996_event A,
      q3526996_metric_open (q3526996_polish_metric S) U ->
      q3526996_borel S U
| q3526996_borel_empty :
    q3526996_borel S q3526996_empty
| q3526996_borel_ext :
    forall E F : q3526996_event A,
      q3526996_borel S E ->
      q3526996_same_event E F ->
      q3526996_borel S F
| q3526996_borel_complement :
    forall E : q3526996_event A,
      q3526996_borel S E ->
      q3526996_borel S (q3526996_complement E)
| q3526996_borel_countable_union :
    forall E : nat -> q3526996_event A,
      (forall n : nat, q3526996_borel S (E n)) ->
      q3526996_borel S (q3526996_countable_union E).

Record q3526996_finite_set (I : Type) : Type := {
  q3526996_finite_member : I -> Prop;
  q3526996_finite_enumeration :
    exists enumeration : list I,
      forall i : I,
        q3526996_finite_member i <-> In i enumeration
}.

Arguments q3526996_finite_member {I} _ _.

Definition q3526996_finite_subset {I : Type}
    (J K : q3526996_finite_set I) : Prop :=
  forall i : I,
    q3526996_finite_member J i ->
    q3526996_finite_member K i.

Record q3526996_finite_tuple
    {I : Type} (alpha : I -> Type)
    (J : q3526996_finite_set I) : Type := {
  q3526996_finite_tuple_value :
    forall i : I, q3526996_finite_member J i -> alpha i;
  q3526996_finite_tuple_membership_irrelevant :
    forall (i : I)
      (p q : q3526996_finite_member J i),
      q3526996_finite_tuple_value i p =
      q3526996_finite_tuple_value i q
}.

Arguments q3526996_finite_tuple_value
  {I alpha J} _ i _.

Definition q3526996_finite_restrict
    {I : Type} {alpha : I -> Type}
    {J K : q3526996_finite_set I}
    (hJK : q3526996_finite_subset J K)
    (x : q3526996_finite_tuple alpha K)
    : q3526996_finite_tuple alpha J :=
  {|
    q3526996_finite_tuple_value :=
      fun i hi =>
        q3526996_finite_tuple_value x i (hJK i hi);
    q3526996_finite_tuple_membership_irrelevant :=
      fun i p q =>
        q3526996_finite_tuple_membership_irrelevant
          x i (hJK i p) (hJK i q)
  |}.

Definition q3526996_full_tuple
    {I : Type} (alpha : I -> Type) : Type :=
  forall i : I, alpha i.

Definition q3526996_full_restrict
    {I : Type} {alpha : I -> Type}
    (J : q3526996_finite_set I)
    (x : q3526996_full_tuple alpha)
    : q3526996_finite_tuple alpha J :=
  {|
    q3526996_finite_tuple_value := fun i _ => x i;
    q3526996_finite_tuple_membership_irrelevant :=
      fun _ _ _ => eq_refl
  |}.

Inductive q3526996_finite_measurable
    {I : Type} {alpha : I -> Type}
    (spaces : forall i : I, q3526996_polish_space (alpha i))
    (J : q3526996_finite_set I)
    : q3526996_event (q3526996_finite_tuple alpha J) -> Prop :=
| q3526996_finite_measurable_coordinate :
    forall (i : I)
      (hi : q3526996_finite_member J i)
      (E : q3526996_event (alpha i)),
      q3526996_borel (spaces i) E ->
      @q3526996_finite_measurable I alpha spaces J
        (fun x =>
          E (q3526996_finite_tuple_value x i hi))
| q3526996_finite_measurable_empty :
    @q3526996_finite_measurable I alpha spaces J q3526996_empty
| q3526996_finite_measurable_ext :
    forall E F :
      q3526996_event (q3526996_finite_tuple alpha J),
      @q3526996_finite_measurable I alpha spaces J E ->
      q3526996_same_event E F ->
      @q3526996_finite_measurable I alpha spaces J F
| q3526996_finite_measurable_complement :
    forall E :
      q3526996_event (q3526996_finite_tuple alpha J),
      @q3526996_finite_measurable I alpha spaces J E ->
      @q3526996_finite_measurable I alpha spaces J
        (q3526996_complement E)
| q3526996_finite_measurable_countable_union :
    forall E :
      nat -> q3526996_event (q3526996_finite_tuple alpha J),
      (forall n : nat,
        @q3526996_finite_measurable I alpha spaces J (E n)) ->
      @q3526996_finite_measurable I alpha spaces J
        (q3526996_countable_union E).

Inductive q3526996_product_measurable
    {I : Type} {alpha : I -> Type}
    (spaces : forall i : I, q3526996_polish_space (alpha i))
    : q3526996_event (q3526996_full_tuple alpha) -> Prop :=
| q3526996_product_measurable_coordinate :
    forall (i : I) (E : q3526996_event (alpha i)),
      q3526996_borel (spaces i) E ->
      @q3526996_product_measurable I alpha spaces
        (fun x => E (x i))
| q3526996_product_measurable_empty :
    @q3526996_product_measurable I alpha spaces q3526996_empty
| q3526996_product_measurable_ext :
    forall E F : q3526996_event (q3526996_full_tuple alpha),
      @q3526996_product_measurable I alpha spaces E ->
      q3526996_same_event E F ->
      @q3526996_product_measurable I alpha spaces F
| q3526996_product_measurable_complement :
    forall E : q3526996_event (q3526996_full_tuple alpha),
      @q3526996_product_measurable I alpha spaces E ->
      @q3526996_product_measurable I alpha spaces
        (q3526996_complement E)
| q3526996_product_measurable_countable_union :
    forall E : nat ->
      q3526996_event (q3526996_full_tuple alpha),
      (forall n : nat,
        @q3526996_product_measurable I alpha spaces (E n)) ->
      @q3526996_product_measurable I alpha spaces
        (q3526996_countable_union E).

Inductive q3526996_ennreal : Type :=
| q3526996_ennreal_finite :
    forall value : R, 0 <= value -> q3526996_ennreal
| q3526996_ennreal_infinity : q3526996_ennreal.

Arguments q3526996_ennreal_finite value nonnegative : clear implicits.

Definition q3526996_ennreal_zero : q3526996_ennreal :=
  q3526996_ennreal_finite 0 (Rle_refl 0).

Definition q3526996_ennreal_eq
    (x y : q3526996_ennreal) : Prop :=
  match x, y with
  | q3526996_ennreal_finite a _,
    q3526996_ennreal_finite b _ => a = b
  | q3526996_ennreal_infinity,
    q3526996_ennreal_infinity => True
  | _, _ => False
  end.

Definition q3526996_ennreal_le
    (x y : q3526996_ennreal) : Prop :=
  match x, y with
  | q3526996_ennreal_finite a _,
    q3526996_ennreal_finite b _ => a <= b
  | q3526996_ennreal_finite _ _,
    q3526996_ennreal_infinity => True
  | q3526996_ennreal_infinity,
    q3526996_ennreal_finite _ _ => False
  | q3526996_ennreal_infinity,
    q3526996_ennreal_infinity => True
  end.

Definition q3526996_ennreal_add
    (x y : q3526996_ennreal) : q3526996_ennreal :=
  match x, y with
  | q3526996_ennreal_finite a ha,
    q3526996_ennreal_finite b hb =>
      q3526996_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q3526996_ennreal_infinity
  end.

Fixpoint q3526996_ennreal_partial_sum
    (u : nat -> q3526996_ennreal)
    (n : nat) : q3526996_ennreal :=
  match n with
  | O => q3526996_ennreal_zero
  | S k =>
      q3526996_ennreal_add
        (q3526996_ennreal_partial_sum u k) (u k)
  end.

Definition q3526996_ennreal_supremum
    (values : q3526996_ennreal -> Prop)
    (bound : q3526996_ennreal) : Prop :=
  (forall value : q3526996_ennreal,
      values value ->
      q3526996_ennreal_le value bound) /\
  (forall upper : q3526996_ennreal,
      (forall value : q3526996_ennreal,
        values value ->
        q3526996_ennreal_le value upper) ->
      q3526996_ennreal_le bound upper).

Definition q3526996_ennreal_series_sum
    (u : nat -> q3526996_ennreal)
    (sum : q3526996_ennreal) : Prop :=
  q3526996_ennreal_supremum
    (fun value =>
      exists n : nat,
        q3526996_ennreal_eq value
          (q3526996_ennreal_partial_sum u n))
    sum.

Record q3526996_measure {A : Type}
    (M : q3526996_event A -> Prop) : Type := {
  q3526996_measure_value :
    q3526996_event A -> q3526996_ennreal;
  q3526996_measure_extensional :
    forall E F : q3526996_event A,
      q3526996_same_event E F ->
      q3526996_ennreal_eq
        (q3526996_measure_value E)
        (q3526996_measure_value F);
  q3526996_measure_empty :
    q3526996_ennreal_eq
      (q3526996_measure_value q3526996_empty)
      q3526996_ennreal_zero;
  q3526996_measure_countably_additive :
    forall E : nat -> q3526996_event A,
      (forall n : nat, M (E n)) ->
      q3526996_pairwise_disjoint E ->
      q3526996_ennreal_series_sum
        (fun n => q3526996_measure_value (E n))
        (q3526996_measure_value
          (q3526996_countable_union E))
}.

Arguments q3526996_measure_value {A M} _ _.

Definition q3526996_finite_measure
    {A : Type} {M : q3526996_event A -> Prop}
    (mu : q3526996_measure M) : Prop :=
  exists value : R,
    exists nonnegative : 0 <= value,
      q3526996_ennreal_eq
        (q3526996_measure_value mu q3526996_full)
        (q3526996_ennreal_finite value nonnegative).

Definition q3526996_measure_family
    {I : Type} {alpha : I -> Type}
    (spaces : forall i : I, q3526996_polish_space (alpha i))
    : Type :=
  forall J : q3526996_finite_set I,
    q3526996_measure
      (@q3526996_finite_measurable I alpha spaces J).

Definition q3526996_is_projective_measure_family
    {I : Type} {alpha : I -> Type}
    {spaces : forall i : I, q3526996_polish_space (alpha i)}
    (P : q3526996_measure_family spaces) : Prop :=
  forall (K J : q3526996_finite_set I)
    (hJK : q3526996_finite_subset J K)
    (E : q3526996_event (q3526996_finite_tuple alpha J)),
    @q3526996_finite_measurable I alpha spaces J E ->
    q3526996_ennreal_eq
      (q3526996_measure_value (P J) E)
      (q3526996_measure_value (P K)
        (fun x =>
          E (q3526996_finite_restrict hJK x))).

Definition q3526996_is_projective_limit
    {I : Type} {alpha : I -> Type}
    {spaces : forall i : I, q3526996_polish_space (alpha i)}
    (mu : q3526996_measure
      (@q3526996_product_measurable I alpha spaces))
    (P : q3526996_measure_family spaces) : Prop :=
  forall (J : q3526996_finite_set I)
    (E : q3526996_event (q3526996_finite_tuple alpha J)),
    @q3526996_finite_measurable I alpha spaces J E ->
    q3526996_ennreal_eq
      (q3526996_measure_value mu
        (fun x => E (q3526996_full_restrict J x)))
      (q3526996_measure_value (P J) E).

Theorem MeasureTheory_isProjectiveLimit_projectiveLimit :
  forall (I : Type) (alpha : I -> Type)
    (spaces : forall i : I,
      q3526996_polish_space (alpha i))
    (P : q3526996_measure_family spaces),
    (forall J : q3526996_finite_set I,
      q3526996_finite_measure (P J)) ->
    q3526996_is_projective_measure_family P ->
    exists mu : q3526996_measure
      (@q3526996_product_measurable I alpha spaces),
      q3526996_is_projective_limit mu P.
Admitted.
