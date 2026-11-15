(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2275191
  (thousand-theorems__rocq__Q2275191), "Lebesgue differentiation theorem":
  for an almost-everywhere measurable extended-nonnegative function with
  finite lower integral, its normalized integrals over sets shrinking to a
  point along a Vitali family converge almost everywhere to the function.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q2275191_set (A : Type) : Type := A -> Prop.

Definition q2275191_empty {A : Type} : q2275191_set A :=
  fun _ => False.

Definition q2275191_full {A : Type} : q2275191_set A :=
  fun _ => True.

Definition q2275191_complement {A : Type}
    (E : q2275191_set A) : q2275191_set A :=
  fun x => ~ E x.

Definition q2275191_intersection {A : Type}
    (E F : q2275191_set A) : q2275191_set A :=
  fun x => E x /\ F x.

Definition q2275191_difference {A : Type}
    (E F : q2275191_set A) : q2275191_set A :=
  fun x => E x /\ ~ F x.

Definition q2275191_countable_union {A : Type}
    (E : nat -> q2275191_set A) : q2275191_set A :=
  fun x => exists n : nat, E n x.

Definition q2275191_same_set {A : Type}
    (E F : q2275191_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q2275191_subset {A : Type}
    (E F : q2275191_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q2275191_disjoint {A : Type}
    (E F : q2275191_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q2275191_pairwise_disjoint_sequence {A : Type}
    (E : nat -> q2275191_set A) : Prop :=
  forall i j : nat,
    i <> j -> q2275191_disjoint (E i) (E j).

Record q2275191_pseudo_metric_space (A : Type) : Type := {
  q2275191_dist : A -> A -> R;
  q2275191_dist_nonnegative :
    forall x y : A, 0 <= q2275191_dist x y;
  q2275191_dist_self :
    forall x : A, q2275191_dist x x = 0;
  q2275191_dist_symmetric :
    forall x y : A, q2275191_dist x y = q2275191_dist y x;
  q2275191_dist_triangle :
    forall x y z : A,
      q2275191_dist x z <=
      q2275191_dist x y + q2275191_dist y z
}.

Arguments q2275191_dist {A} _ _ _.

Definition q2275191_open_ball {A : Type}
    (M : q2275191_pseudo_metric_space A)
    (center : A) (radius : R) : q2275191_set A :=
  fun x => q2275191_dist M x center < radius.

Definition q2275191_closed_ball {A : Type}
    (M : q2275191_pseudo_metric_space A)
    (center : A) (radius : R) : q2275191_set A :=
  fun x => q2275191_dist M x center <= radius.

Definition q2275191_open {A : Type}
    (M : q2275191_pseudo_metric_space A)
    (U : q2275191_set A) : Prop :=
  forall x : A,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      q2275191_subset
        (q2275191_open_ball M x epsilon) U.

Definition q2275191_nonempty_interior {A : Type}
    (M : q2275191_pseudo_metric_space A)
    (E : q2275191_set A) : Prop :=
  exists (x : A) (epsilon : R),
    0 < epsilon /\
    q2275191_subset
      (q2275191_open_ball M x epsilon) E.

Definition q2275191_second_countable {A : Type}
    (M : q2275191_pseudo_metric_space A) : Prop :=
  exists basis : nat -> q2275191_set A,
    (forall n : nat, q2275191_open M (basis n)) /\
    forall (U : q2275191_set A) (x : A),
      q2275191_open M U ->
      U x ->
      exists n : nat,
        basis n x /\ q2275191_subset (basis n) U.

Inductive q2275191_ennreal : Type :=
| q2275191_ennreal_finite :
    forall value : R, 0 <= value -> q2275191_ennreal
| q2275191_ennreal_infinity : q2275191_ennreal.

Arguments q2275191_ennreal_finite value nonnegative : clear implicits.

Definition q2275191_ennreal_zero : q2275191_ennreal :=
  q2275191_ennreal_finite 0 (Rle_refl 0).

Definition q2275191_ennreal_eq
    (x y : q2275191_ennreal) : Prop :=
  match x, y with
  | q2275191_ennreal_finite a _,
    q2275191_ennreal_finite b _ => a = b
  | q2275191_ennreal_infinity,
    q2275191_ennreal_infinity => True
  | _, _ => False
  end.

Definition q2275191_ennreal_le
    (x y : q2275191_ennreal) : Prop :=
  match x, y with
  | q2275191_ennreal_finite a _,
    q2275191_ennreal_finite b _ => a <= b
  | q2275191_ennreal_finite _ _,
    q2275191_ennreal_infinity => True
  | q2275191_ennreal_infinity,
    q2275191_ennreal_finite _ _ => False
  | q2275191_ennreal_infinity,
    q2275191_ennreal_infinity => True
  end.

Definition q2275191_ennreal_lt
    (x y : q2275191_ennreal) : Prop :=
  match x, y with
  | q2275191_ennreal_finite a _,
    q2275191_ennreal_finite b _ => a < b
  | q2275191_ennreal_finite _ _,
    q2275191_ennreal_infinity => True
  | _, _ => False
  end.

Definition q2275191_ennreal_below_real
    (x : q2275191_ennreal) (bound : R) : Prop :=
  match x with
  | q2275191_ennreal_finite value _ => value < bound
  | q2275191_ennreal_infinity => False
  end.

Definition q2275191_ennreal_above_real
    (x : q2275191_ennreal) (bound : R) : Prop :=
  match x with
  | q2275191_ennreal_finite value _ => bound < value
  | q2275191_ennreal_infinity => True
  end.

Definition q2275191_ennreal_add
    (x y : q2275191_ennreal) : q2275191_ennreal :=
  match x, y with
  | q2275191_ennreal_finite a ha,
    q2275191_ennreal_finite b hb =>
      q2275191_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q2275191_ennreal_infinity
  end.

Definition q2275191_ennreal_mul
    (x y : q2275191_ennreal) : q2275191_ennreal :=
  match x, y with
  | q2275191_ennreal_finite a ha,
    q2275191_ennreal_finite b hb =>
      q2275191_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q2275191_ennreal_finite a _, q2275191_ennreal_infinity
  | q2275191_ennreal_infinity, q2275191_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q2275191_ennreal_zero
      else q2275191_ennreal_infinity
  | q2275191_ennreal_infinity, q2275191_ennreal_infinity =>
      q2275191_ennreal_infinity
  end.

Definition q2275191_div_nonnegative
    (a b : R) (ha : 0 <= a) (hb : 0 <= b)
    (hb0 : b <> 0) : 0 <= a / b :=
  eq_ind_r
    (fun value : R => 0 <= value)
    (Rmult_le_pos a (/ b) ha
      (Rlt_le 0 (/ b)
        (Rinv_0_lt_compat b
          (match Rle_lt_or_eq_dec 0 b hb with
           | left positive => positive
           | right zero =>
               False_rect (0 < b) (hb0 (eq_sym zero))
           end))))
    (Rdiv_def a b).

Definition q2275191_ennreal_div
    (x y : q2275191_ennreal) : q2275191_ennreal :=
  match x, y with
  | q2275191_ennreal_finite a ha,
    q2275191_ennreal_finite b hb =>
      match Req_EM_T b 0 with
      | left _ =>
          match Req_EM_T a 0 with
          | left _ => q2275191_ennreal_zero
          | right _ => q2275191_ennreal_infinity
          end
      | right hb0 =>
          q2275191_ennreal_finite
            (a / b)
            (@q2275191_div_nonnegative a b ha hb hb0)
      end
  | q2275191_ennreal_finite _ _,
    q2275191_ennreal_infinity =>
      q2275191_ennreal_zero
  | q2275191_ennreal_infinity,
    q2275191_ennreal_finite _ _ =>
      q2275191_ennreal_infinity
  | q2275191_ennreal_infinity,
    q2275191_ennreal_infinity =>
      q2275191_ennreal_zero
  end.

Fixpoint q2275191_ennreal_partial_sum
    (u : nat -> q2275191_ennreal)
    (n : nat) : q2275191_ennreal :=
  match n with
  | O => q2275191_ennreal_zero
  | S k =>
      q2275191_ennreal_add
        (q2275191_ennreal_partial_sum u k) (u k)
  end.

Definition q2275191_ennreal_supremum
    (values : q2275191_ennreal -> Prop)
    (bound : q2275191_ennreal) : Prop :=
  (forall value : q2275191_ennreal,
      values value -> q2275191_ennreal_le value bound) /\
  (forall upper : q2275191_ennreal,
      (forall value : q2275191_ennreal,
        values value -> q2275191_ennreal_le value upper) ->
      q2275191_ennreal_le bound upper).

Definition q2275191_ennreal_series_sum
    (u : nat -> q2275191_ennreal)
    (sum : q2275191_ennreal) : Prop :=
  q2275191_ennreal_supremum
    (fun value =>
      exists n : nat,
        q2275191_ennreal_eq value
          (q2275191_ennreal_partial_sum u n))
    sum.

Record q2275191_measurable_space (A : Type) : Type := {
  q2275191_measurable : q2275191_set A -> Prop;
  q2275191_measurable_extensional :
    forall E F : q2275191_set A,
      q2275191_same_set E F ->
      (q2275191_measurable E <-> q2275191_measurable F);
  q2275191_measurable_empty :
    q2275191_measurable q2275191_empty;
  q2275191_measurable_complement :
    forall E : q2275191_set A,
      q2275191_measurable E ->
      q2275191_measurable (q2275191_complement E);
  q2275191_measurable_countable_union :
    forall E : nat -> q2275191_set A,
      (forall n : nat, q2275191_measurable (E n)) ->
      q2275191_measurable (q2275191_countable_union E)
}.

Arguments q2275191_measurable {A} _ _.

Definition q2275191_borel_measurable {A : Type}
    (M : q2275191_pseudo_metric_space A)
    (E : q2275191_set A) : Prop :=
  forall sigma : q2275191_measurable_space A,
    (forall U : q2275191_set A,
      q2275191_open M U ->
      q2275191_measurable sigma U) ->
    q2275191_measurable sigma E.

Definition q2275191_borel_space {A : Type}
    (M : q2275191_pseudo_metric_space A)
    (m : q2275191_measurable_space A) : Prop :=
  forall E : q2275191_set A,
    q2275191_measurable m E <->
    q2275191_borel_measurable M E.

Record q2275191_measure {A : Type}
    (m : q2275191_measurable_space A) : Type := {
  q2275191_measure_value : q2275191_set A -> q2275191_ennreal;
  q2275191_measure_extensional :
    forall E F : q2275191_set A,
      q2275191_same_set E F ->
      q2275191_ennreal_eq
        (q2275191_measure_value E)
        (q2275191_measure_value F);
  q2275191_measure_empty :
    q2275191_ennreal_eq
      (q2275191_measure_value q2275191_empty)
      q2275191_ennreal_zero;
  q2275191_measure_monotone :
    forall E F : q2275191_set A,
      q2275191_subset E F ->
      q2275191_ennreal_le
        (q2275191_measure_value E)
        (q2275191_measure_value F);
  q2275191_measure_trim :
    forall E : q2275191_set A,
      exists F : q2275191_set A,
        q2275191_measurable m F /\
        q2275191_subset E F /\
        q2275191_ennreal_eq
          (q2275191_measure_value F)
          (q2275191_measure_value E);
  q2275191_measure_countable_subadditive :
    forall E : nat -> q2275191_set A,
      exists total : q2275191_ennreal,
        q2275191_ennreal_series_sum
          (fun n => q2275191_measure_value (E n)) total /\
        q2275191_ennreal_le
          (q2275191_measure_value
            (q2275191_countable_union E))
          total;
  q2275191_measure_countable_additive :
    forall E : nat -> q2275191_set A,
      (forall n : nat, q2275191_measurable m (E n)) ->
      q2275191_pairwise_disjoint_sequence E ->
      q2275191_ennreal_series_sum
        (fun n => q2275191_measure_value (E n))
        (q2275191_measure_value
          (q2275191_countable_union E))
}.

Arguments q2275191_measure_value {A m} _ _.

Definition q2275191_almost_everywhere {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (P : A -> Prop) : Prop :=
  exists null_set : q2275191_set A,
    q2275191_measurable m null_set /\
    q2275191_ennreal_eq
      (q2275191_measure_value mu null_set)
      q2275191_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Definition q2275191_locally_finite {A : Type}
    (M : q2275191_pseudo_metric_space A)
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m) : Prop :=
  forall x : A,
    exists U : q2275191_set A,
      q2275191_open M U /\
      U x /\
      q2275191_ennreal_lt
        (q2275191_measure_value mu U)
        q2275191_ennreal_infinity.

Definition q2275191_measurable_ennreal_function {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (f : A -> q2275191_ennreal) : Prop :=
  forall bound : R,
    q2275191_measurable m
      (fun x => q2275191_ennreal_below_real (f x) bound).

Definition q2275191_ae_measurable_ennreal_function {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (f : A -> q2275191_ennreal) : Prop :=
  exists g : A -> q2275191_ennreal,
    q2275191_measurable_ennreal_function mu g /\
    q2275191_almost_everywhere mu
      (fun x => q2275191_ennreal_eq (f x) (g x)).

Definition q2275191_finite_partition {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (k : nat) (cells : nat -> q2275191_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q2275191_measurable m (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q2275191_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Record q2275191_nonnegative_real : Type := {
  q2275191_nnreal_value : R;
  q2275191_nnreal_nonnegative : 0 <= q2275191_nnreal_value
}.

Definition q2275191_ennreal_of_nonnegative
    (x : q2275191_nonnegative_real) : q2275191_ennreal :=
  q2275191_ennreal_finite
    (q2275191_nnreal_value x)
    (q2275191_nnreal_nonnegative x).

Definition q2275191_simple_lintegral_below {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (f : A -> q2275191_ennreal)
    (value : q2275191_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q2275191_nonnegative_real)
         (cells : nat -> q2275191_set A),
    q2275191_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q2275191_ennreal_le
        (q2275191_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q2275191_ennreal_eq value
      (q2275191_ennreal_partial_sum
        (fun i =>
          q2275191_ennreal_mul
            (q2275191_ennreal_of_nonnegative (coefficients i))
            (q2275191_measure_value mu (cells i)))
        k).

Definition q2275191_lintegral_has_value {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (f : A -> q2275191_ennreal)
    (value : q2275191_ennreal) : Prop :=
  q2275191_ennreal_supremum
    (q2275191_simple_lintegral_below mu f) value.

Definition q2275191_lintegral_not_infinite {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (f : A -> q2275191_ennreal) : Prop :=
  exists value : q2275191_ennreal,
    q2275191_lintegral_has_value mu f value /\
    ~ q2275191_ennreal_eq
        value q2275191_ennreal_infinity.

Definition q2275191_indicator {A : Type}
    (E : q2275191_set A)
    (f : A -> q2275191_ennreal)
    (x : A) : q2275191_ennreal :=
  if excluded_middle_informative (E x)
  then f x
  else q2275191_ennreal_zero.

Definition q2275191_restricted_lintegral_has_value {A : Type}
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m)
    (f : A -> q2275191_ennreal)
    (E : q2275191_set A)
    (value : q2275191_ennreal) : Prop :=
  q2275191_lintegral_has_value mu
    (q2275191_indicator E f) value.

Definition q2275191_pairwise_disjoint_selected {A : Type}
    (selected : q2275191_set (A * q2275191_set A)) : Prop :=
  forall p q : A * q2275191_set A,
    selected p ->
    selected q ->
    p <> q ->
    q2275191_disjoint (snd p) (snd q).

Definition q2275191_selected_union {A : Type}
    (selected : q2275191_set (A * q2275191_set A))
    : q2275191_set A :=
  fun x =>
    exists p : A * q2275191_set A,
      selected p /\ snd p x.

Record q2275191_vitali_family {A : Type}
    (M : q2275191_pseudo_metric_space A)
    {m : q2275191_measurable_space A}
    (mu : q2275191_measure m) : Type := {
  q2275191_sets_at :
    A -> q2275191_set (q2275191_set A);
  q2275191_vitali_measurable :
    forall (x : A) (E : q2275191_set A),
      q2275191_sets_at x E ->
      q2275191_measurable m E;
  q2275191_vitali_nonempty_interior :
    forall (x : A) (E : q2275191_set A),
      q2275191_sets_at x E ->
      q2275191_nonempty_interior M E;
  q2275191_vitali_nontrivial :
    forall (x : A) (epsilon : R),
      0 < epsilon ->
      exists E : q2275191_set A,
        q2275191_sets_at x E /\
        q2275191_subset E
          (q2275191_closed_ball M x epsilon);
  q2275191_vitali_covering :
    forall (s : q2275191_set A)
           (family : A -> q2275191_set (q2275191_set A)),
      (forall (x : A) (E : q2275191_set A),
        s x ->
        family x E ->
        q2275191_sets_at x E) ->
      (forall (x : A) (epsilon : R),
        s x ->
        0 < epsilon ->
        exists E : q2275191_set A,
          family x E /\
          q2275191_subset E
            (q2275191_closed_ball M x epsilon)) ->
      exists selected :
          q2275191_set (A * q2275191_set A),
        (forall p : A * q2275191_set A,
          selected p -> s (fst p)) /\
        q2275191_pairwise_disjoint_selected selected /\
        (forall p : A * q2275191_set A,
          selected p -> family (fst p) (snd p)) /\
        q2275191_ennreal_eq
          (q2275191_measure_value mu
            (q2275191_difference s
              (q2275191_selected_union selected)))
          q2275191_ennreal_zero
}.

Arguments q2275191_sets_at {A M m mu} _ _ _.

Definition q2275191_eventually_vitali {A : Type}
    (M : q2275191_pseudo_metric_space A)
    {m : q2275191_measurable_space A}
    {mu : q2275191_measure m}
    (v : q2275191_vitali_family M mu)
    (x : A)
    (P : q2275191_set A -> Prop) : Prop :=
  exists epsilon : R,
    0 < epsilon /\
    forall E : q2275191_set A,
      q2275191_sets_at v x E ->
      q2275191_subset E
        (q2275191_closed_ball M x epsilon) ->
      P E.

Definition q2275191_tendsto_vitali_ennreal {A : Type}
    (M : q2275191_pseudo_metric_space A)
    {m : q2275191_measurable_space A}
    {mu : q2275191_measure m}
    (v : q2275191_vitali_family M mu)
    (x : A)
    (u : q2275191_set A -> q2275191_ennreal)
    (limit : q2275191_ennreal) : Prop :=
  match limit with
  | q2275191_ennreal_finite value _ =>
      forall epsilon : R,
        0 < epsilon ->
        @q2275191_eventually_vitali A M m mu v x
          (fun E =>
            match u E with
            | q2275191_ennreal_finite term _ =>
                Rabs (term - value) < epsilon
            | q2275191_ennreal_infinity => False
            end)
  | q2275191_ennreal_infinity =>
      forall bound : R,
        @q2275191_eventually_vitali A M m mu v x
          (fun E =>
            q2275191_ennreal_above_real (u E) bound)
  end.

Theorem VitaliFamily_ae_tendsto_lintegral_div :
  forall (Alpha : Type)
         (M : q2275191_pseudo_metric_space Alpha)
         (m : q2275191_measurable_space Alpha)
         (mu : q2275191_measure m)
         (v : q2275191_vitali_family M mu)
         (f : Alpha -> q2275191_ennreal),
    q2275191_second_countable M ->
    q2275191_borel_space M m ->
    q2275191_locally_finite M mu ->
    q2275191_ae_measurable_ennreal_function mu f ->
    q2275191_lintegral_not_infinite mu f ->
    exists restricted_integral :
        q2275191_set Alpha -> q2275191_ennreal,
      (forall E : q2275191_set Alpha,
        q2275191_restricted_lintegral_has_value
          mu f E (restricted_integral E)) /\
      q2275191_almost_everywhere mu
        (fun x =>
          @q2275191_tendsto_vitali_ennreal
            Alpha M m mu v x
            (fun E =>
              q2275191_ennreal_div
                (restricted_integral E)
                (q2275191_measure_value mu E))
            (f x)).
Admitted.
