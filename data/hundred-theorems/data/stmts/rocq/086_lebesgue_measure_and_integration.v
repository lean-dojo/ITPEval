(*
  Statement-only formalization of "Lebesgue Measure and Integration" from
  Hundred Theorems artifact 086. It specifies Borel and Lebesgue measure,
  nonnegative and signed Lebesgue integrals, and their principal convergence,
  sigma-finite product-integration, and local differentiation laws.
  This file contains no proof.
*)

From Stdlib Require Import Reals List ClassicalDescription.

Set Implicit Arguments.
#[local] Open Scope R_scope.

Definition set (A : Type) := A -> Prop.

Definition empty_set {A : Type} : set A :=
  fun _ => False.

Definition full_set {A : Type} : set A :=
  fun _ => True.

Definition set_complement {A : Type} (E : set A) : set A :=
  fun x => ~ E x.

Definition countable_union {A : Type} (E : nat -> set A) : set A :=
  fun x => exists n : nat, E n x.

Definition same_set {A : Type} (E F : set A) : Prop :=
  forall x : A, E x <-> F x.

Definition disjoint_sets {A : Type} (E F : set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition pairwise_disjoint {A : Type} (E : nat -> set A) : Prop :=
  forall i j : nat, i <> j -> disjoint_sets (E i) (E j).

Definition sigma_class {A : Type} (C : set (set A)) : Prop :=
  C empty_set /\
  (forall E : set A, C E -> C (set_complement E)) /\
  (forall E : nat -> set A,
      (forall n : nat, C (E n)) ->
      C (countable_union E)).

Definition open_real_set (U : set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R, Rabs (y - x) < epsilon -> U y.

Definition borel_set (E : set R) : Prop :=
  forall C : set (set R),
    sigma_class C ->
    (forall U : set R, open_real_set U -> C U) ->
    C E.

Inductive extended_nonnegative : Type :=
| ennreal_finite :
    forall value : R, 0 <= value -> extended_nonnegative
| ennreal_infinity : extended_nonnegative.

Arguments ennreal_finite value nonnegative : clear implicits.

Definition ennreal_zero : extended_nonnegative :=
  ennreal_finite 0 (Rle_refl 0).

Definition ennreal_one : extended_nonnegative :=
  ennreal_finite 1 Rle_0_1.

Record nonnegative_real : Type := {
  nnreal_value : R;
  nnreal_nonnegative : 0 <= nnreal_value
}.

Definition ennreal_of_nonnegative
    (x : nonnegative_real) : extended_nonnegative :=
  ennreal_finite (nnreal_value x) (nnreal_nonnegative x).

Definition ennreal_represents
    (x : extended_nonnegative) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    x = ennreal_finite value nonnegative.

Definition ennreal_finite_value (x : extended_nonnegative) : Prop :=
  exists value : R, ennreal_represents x value.

Definition ennreal_le
    (x y : extended_nonnegative) : Prop :=
  match x, y with
  | ennreal_finite a _, ennreal_finite b _ => a <= b
  | ennreal_finite _ _, ennreal_infinity => True
  | ennreal_infinity, ennreal_finite _ _ => False
  | ennreal_infinity, ennreal_infinity => True
  end.

Definition ennreal_add
  (x y : extended_nonnegative) : extended_nonnegative :=
  match x, y with
  | ennreal_finite a a_nonnegative,
    ennreal_finite b b_nonnegative =>
      ennreal_finite (a + b)
        (Rplus_le_le_0_compat a b a_nonnegative b_nonnegative)
  | _, _ => ennreal_infinity
  end.

Definition ennreal_mul
  (x y : extended_nonnegative) : extended_nonnegative :=
  match x, y with
  | ennreal_finite a a_nonnegative,
    ennreal_finite b b_nonnegative =>
      ennreal_finite (a * b)
        (Rmult_le_pos a b a_nonnegative b_nonnegative)
  | ennreal_finite a _, ennreal_infinity
  | ennreal_infinity, ennreal_finite a _ =>
      if Req_EM_T a 0 then ennreal_zero else ennreal_infinity
  | ennreal_infinity, ennreal_infinity => ennreal_infinity
  end.

Definition ennreal_scale
    (c x : extended_nonnegative) : extended_nonnegative :=
  ennreal_mul c x.

Fixpoint ennreal_partial_sum
    (u : nat -> extended_nonnegative) (n : nat) : extended_nonnegative :=
  match n with
  | O => ennreal_zero
  | S k => ennreal_add (ennreal_partial_sum u k) (u k)
  end.

Definition ennreal_supremum
    (values : extended_nonnegative -> Prop)
    (bound : extended_nonnegative) : Prop :=
  (forall value : extended_nonnegative,
      values value -> ennreal_le value bound) /\
  (forall upper : extended_nonnegative,
      (forall value : extended_nonnegative,
          values value -> ennreal_le value upper) ->
      ennreal_le bound upper).

Definition ennreal_series_sum
    (u : nat -> extended_nonnegative)
    (sum : extended_nonnegative) : Prop :=
  ennreal_supremum
    (fun value =>
      exists n : nat, value = ennreal_partial_sum u n)
    sum.

Record measure_space (A : Type) := {
  measurable : set A -> Prop;
  measurable_empty : measurable empty_set;
  measurable_complement :
    forall E : set A,
      measurable E ->
      measurable (set_complement E);
  measurable_countable_union :
    forall E : nat -> set A,
      (forall n : nat, measurable (E n)) ->
      measurable (countable_union E);
  measure : set A -> extended_nonnegative;
  measure_extensional :
    forall E F : set A,
      same_set E F ->
      measure E = measure F;
  measure_empty : measure empty_set = ennreal_zero;
  measure_countable_additive :
    forall E : nat -> set A,
      (forall n : nat, measurable (E n)) ->
      pairwise_disjoint E ->
      ennreal_series_sum
        (fun n => measure (E n))
        (measure (countable_union E))
}.

Definition is_borel_measure (mu : measure_space R) : Prop :=
  forall E : set R, measurable mu E <-> borel_set E.

Definition half_open_interval (a b : R) : set R :=
  fun x => a <= x < b.

Definition is_lebesgue_measure (mu : measure_space R) : Prop :=
  is_borel_measure mu /\
  forall a b : R,
    a <= b ->
    ennreal_represents
      (measure mu (half_open_interval a b)) (b - a).

Theorem lebesgue_measure_exists_unique :
  exists mu : measure_space R,
    is_lebesgue_measure mu /\
    forall nu : measure_space R,
      is_lebesgue_measure nu ->
      forall E : set R,
        borel_set E ->
        measure mu E = measure nu E.
Proof.
Admitted.

Definition ennreal_below
    (x : extended_nonnegative) (bound : R) : Prop :=
  match x with
  | ennreal_finite value _ => value < bound
  | ennreal_infinity => False
  end.

Definition measurable_ennreal_function {A : Type}
    (mu : measure_space A) (f : A -> extended_nonnegative) : Prop :=
  forall bound : R,
    measurable mu (fun x => ennreal_below (f x) bound).

Definition measurable_real_function {A : Type}
    (mu : measure_space A) (f : A -> R) : Prop :=
  forall bound : R,
    measurable mu (fun x => f x < bound).

Definition finite_partition {A : Type}
    (mu : measure_space A)
    (n : nat) (cells : nat -> set A) : Prop :=
  (0 < n)%nat /\
  (forall i : nat, (i < n)%nat -> measurable mu (cells i)) /\
  (forall i j : nat,
      (i < n)%nat ->
      (j < n)%nat ->
      i <> j ->
      disjoint_sets (cells i) (cells j)) /\
  (forall x : A,
      exists i : nat, (i < n)%nat /\ cells i x).

Definition simple_integral_below {A : Type}
    (mu : measure_space A)
    (f : A -> extended_nonnegative)
    (value : extended_nonnegative) : Prop :=
  exists (n : nat)
         (coefficients : nat -> nonnegative_real)
         (cells : nat -> set A),
    finite_partition mu n cells /\
    (forall (x : A) (i : nat),
      (i < n)%nat ->
      cells i x ->
      ennreal_le (ennreal_of_nonnegative (coefficients i)) (f x)) /\
    value =
      ennreal_partial_sum
        (fun i =>
          ennreal_scale
            (ennreal_of_nonnegative (coefficients i))
            (measure mu (cells i)))
        n.

Definition lintegral_has_value {A : Type}
    (mu : measure_space A)
    (f : A -> extended_nonnegative)
    (value : extended_nonnegative) : Prop :=
  ennreal_supremum (simple_integral_below mu f) value.

Definition ennreal_indicator {A : Type}
    (E : set A) (f : A -> extended_nonnegative)
    (x : A) : extended_nonnegative :=
  if excluded_middle_informative (E x) then f x else ennreal_zero.

Definition set_lintegral_has_value {A : Type}
    (mu : measure_space A) (E : set A)
    (f : A -> extended_nonnegative)
    (value : extended_nonnegative) : Prop :=
  lintegral_has_value mu (ennreal_indicator E f) value.

Theorem lintegral_exists :
  forall (A : Type) (mu : measure_space A)
         (f : A -> extended_nonnegative),
    exists value : extended_nonnegative,
      lintegral_has_value mu f value.
Proof.
Admitted.

Theorem lintegral_unique :
  forall (A : Type) (mu : measure_space A)
         (f : A -> extended_nonnegative)
         (left right : extended_nonnegative),
    lintegral_has_value mu f left ->
    lintegral_has_value mu f right ->
    left = right.
Proof.
Admitted.

Theorem lintegral_indicator_one :
  forall (A : Type) (mu : measure_space A) (E : set A),
    measurable mu E ->
    lintegral_has_value
      mu (ennreal_indicator E (fun _ => ennreal_one))
      (measure mu E).
Proof.
Admitted.

Theorem lintegral_monotone :
  forall (A : Type) (mu : measure_space A)
         (f g : A -> extended_nonnegative)
         (f_integral g_integral : extended_nonnegative),
    (forall x : A, ennreal_le (f x) (g x)) ->
    lintegral_has_value mu f f_integral ->
    lintegral_has_value mu g g_integral ->
    ennreal_le f_integral g_integral.
Proof.
Admitted.

Theorem lintegral_add :
  forall (A : Type) (mu : measure_space A)
         (f g : A -> extended_nonnegative)
         (f_integral g_integral : extended_nonnegative),
    measurable_ennreal_function mu f ->
    measurable_ennreal_function mu g ->
    lintegral_has_value mu f f_integral ->
    lintegral_has_value mu g g_integral ->
    lintegral_has_value mu
      (fun x => ennreal_add (f x) (g x))
      (ennreal_add f_integral g_integral).
Proof.
Admitted.

Theorem lintegral_scale :
  forall (A : Type) (mu : measure_space A)
         (f : A -> extended_nonnegative)
         (c value : extended_nonnegative),
    measurable_ennreal_function mu f ->
    lintegral_has_value mu f value ->
    lintegral_has_value mu
      (fun x => ennreal_scale c (f x))
      (ennreal_scale c value).
Proof.
Admitted.

Definition pointwise_ennreal_monotone {A : Type}
    (f : nat -> A -> extended_nonnegative) : Prop :=
  forall (n : nat) (x : A),
    ennreal_le (f n x) (f (S n) x).

Definition pointwise_ennreal_supremum {A : Type}
    (f : nat -> A -> extended_nonnegative)
    (limit : A -> extended_nonnegative) : Prop :=
  forall x : A,
    ennreal_supremum
      (fun value =>
        exists n : nat, value = f n x)
      (limit x).

Theorem lintegral_monotone_convergence :
  forall (A : Type) (mu : measure_space A)
         (f : nat -> A -> extended_nonnegative)
         (limit : A -> extended_nonnegative)
         (integrals : nat -> extended_nonnegative)
         (limit_integral : extended_nonnegative),
    (forall n : nat, measurable_ennreal_function mu (f n)) ->
    pointwise_ennreal_monotone f ->
    pointwise_ennreal_supremum f limit ->
    (forall n : nat, lintegral_has_value mu (f n) (integrals n)) ->
    ennreal_supremum
      (fun value =>
        exists n : nat, value = integrals n)
      limit_integral ->
    lintegral_has_value mu limit limit_integral.
Proof.
Admitted.

Definition positive_part (x : R) : R :=
  Rmax x 0.

Definition negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition absolute_ennreal (x : R) : extended_nonnegative :=
  ennreal_finite (Rabs x) (Rabs_pos x).

Definition positive_ennreal (x : R) : extended_nonnegative :=
  ennreal_finite (positive_part x) (Rmax_r x 0).

Definition negative_ennreal (x : R) : extended_nonnegative :=
  ennreal_finite (negative_part x) (Rmax_r (- x) 0).

Definition integrable {A : Type}
    (mu : measure_space A) (f : A -> R) : Prop :=
  measurable_real_function mu f /\
  exists value : extended_nonnegative,
    lintegral_has_value mu (fun x => absolute_ennreal (f x)) value /\
    ennreal_finite_value value.

Definition lebesgue_integral_has_value {A : Type}
    (mu : measure_space A) (f : A -> R) (value : R) : Prop :=
  measurable_real_function mu f /\
  exists (positive_integral negative_integral : extended_nonnegative)
         (positive_value negative_value : R),
    lintegral_has_value mu
      (fun x => positive_ennreal (f x)) positive_integral /\
    lintegral_has_value mu
      (fun x => negative_ennreal (f x)) negative_integral /\
    ennreal_represents positive_integral positive_value /\
    ennreal_represents negative_integral negative_value /\
    value = positive_value - negative_value.

Definition real_indicator {A : Type}
    (E : set A) (f : A -> R) (x : A) : R :=
  if excluded_middle_informative (E x) then f x else 0.

Definition set_integral_has_value {A : Type}
    (mu : measure_space A) (E : set A)
    (f : A -> R) (value : R) : Prop :=
  lebesgue_integral_has_value mu (real_indicator E f) value.

Definition integrable_on {A : Type}
    (mu : measure_space A) (E : set A) (f : A -> R) : Prop :=
  integrable mu (real_indicator E f).

Theorem integrable_has_unique_integral :
  forall (A : Type) (mu : measure_space A) (f : A -> R),
    integrable mu f ->
    exists value : R,
      lebesgue_integral_has_value mu f value /\
      forall other : R,
        lebesgue_integral_has_value mu f other ->
        other = value.
Proof.
Admitted.

Theorem lebesgue_integral_add :
  forall (A : Type) (mu : measure_space A)
         (f g : A -> R) (f_value g_value : R),
    lebesgue_integral_has_value mu f f_value ->
    lebesgue_integral_has_value mu g g_value ->
    lebesgue_integral_has_value mu
      (fun x => f x + g x) (f_value + g_value).
Proof.
Admitted.

Theorem lebesgue_integral_scale :
  forall (A : Type) (mu : measure_space A)
         (f : A -> R) (c value : R),
    lebesgue_integral_has_value mu f value ->
    lebesgue_integral_has_value mu
      (fun x => c * f x) (c * value).
Proof.
Admitted.

Definition almost_everywhere {A : Type}
    (mu : measure_space A) (property : A -> Prop) : Prop :=
  exists null_set : set A,
    measurable mu null_set /\
    measure mu null_set = ennreal_zero /\
    forall x : A, ~ property x -> null_set x.

Definition real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Theorem lebesgue_integral_dominated_convergence :
  forall (A : Type) (mu : measure_space A)
         (f : nat -> A -> R) (limit dominating : A -> R),
    (forall n : nat, measurable_real_function mu (f n)) ->
    measurable_real_function mu limit ->
    integrable mu dominating ->
    almost_everywhere mu
      (fun x =>
        forall n : nat, Rabs (f n x) <= dominating x) ->
    almost_everywhere mu
      (fun x =>
        real_sequence_converges (fun n => f n x) (limit x)) ->
    integrable mu limit /\
    exists (values : nat -> R) (limit_value : R),
      (forall n : nat,
        lebesgue_integral_has_value mu (f n) (values n)) /\
      lebesgue_integral_has_value mu limit limit_value /\
      real_sequence_converges values limit_value.
Proof.
Admitted.

Definition rectangle {A B : Type}
    (E : set A) (F : set B) : set (A * B) :=
  fun pair => E (fst pair) /\ F (snd pair).

Definition product_measurable_set {A B : Type}
    (mu : measure_space A) (nu : measure_space B)
    (S : set (A * B)) : Prop :=
  forall C : set (set (A * B)),
    sigma_class C ->
    (forall (E : set A) (F : set B),
      measurable mu E ->
      measurable nu F ->
      C (rectangle E F)) ->
    C S.

Definition is_product_measure {A B : Type}
    (mu : measure_space A) (nu : measure_space B)
    (product : measure_space (A * B)) : Prop :=
  (forall S : set (A * B),
    measurable product S <-> product_measurable_set mu nu S) /\
  (forall (E : set A) (F : set B),
    measurable mu E ->
    measurable nu F ->
    measure product (rectangle E F) =
      ennreal_mul (measure mu E) (measure nu F)).

Definition sigma_finite {A : Type}
    (mu : measure_space A) : Prop :=
  exists cover : nat -> set A,
    (forall n : nat, measurable mu (cover n)) /\
    (forall n : nat, ennreal_finite_value (measure mu (cover n))) /\
    (forall x : A, exists n : nat, cover n x).

Theorem lebesgue_integral_fubini :
  forall (A B : Type)
         (mu : measure_space A) (nu : measure_space B)
         (product : measure_space (A * B))
         (f : A * B -> R),
    sigma_finite mu ->
    sigma_finite nu ->
    is_product_measure mu nu product ->
    integrable product f ->
    exists (integrate_y : A -> R)
           (integrate_x : B -> R)
           (total : R),
      almost_everywhere mu
        (fun x =>
          lebesgue_integral_has_value nu
            (fun y => f (x, y)) (integrate_y x)) /\
      almost_everywhere nu
        (fun y =>
          lebesgue_integral_has_value mu
            (fun x => f (x, y)) (integrate_x y)) /\
      integrable mu integrate_y /\
      integrable nu integrate_x /\
      lebesgue_integral_has_value product f total /\
      lebesgue_integral_has_value mu integrate_y total /\
      lebesgue_integral_has_value nu integrate_x total.
Proof.
Admitted.

Definition open_interval (a b : R) : set R :=
  fun x => a < x < b.

Definition locally_integrable
    (mu : measure_space R) (f : R -> R) : Prop :=
  forall a b : R,
    a < b ->
    integrable_on mu (open_interval a b) f.

Definition interval_average_converges
    (mu : measure_space R) (f : R -> R) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall radius : R,
        0 < radius < delta ->
        exists interval_integral : R,
          set_integral_has_value mu
            (open_interval (x - radius) (x + radius))
            f interval_integral /\
          Rabs (interval_integral / (2 * radius) - f x) < epsilon.

Theorem lebesgue_integral_differentiation :
  forall (mu : measure_space R) (f : R -> R),
    is_lebesgue_measure mu ->
    locally_integrable mu f ->
    almost_everywhere mu (interval_average_converges mu f).
Proof.
Admitted.
