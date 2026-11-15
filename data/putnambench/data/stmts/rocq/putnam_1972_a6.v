(* Statement-only formalization of PutnamBench artifact putnam_1972_a6:
   vanishing lower moments and a normalized nth moment force an integrable
   real function on [0,1] to be large on a set of positive Lebesgue measure.
   This file contains no proof. *)

From Stdlib Require Import Reals ClassicalDescription.

Set Implicit Arguments.
#[local] Open Scope R_scope.

Definition set (A : Type) := A -> Prop.

Definition empty_set {A : Type} : set A :=
  fun _ => False.

Definition set_complement {A : Type} (E : set A) : set A :=
  fun x => ~ E x.

Definition countable_union {A : Type} (E : nat -> set A) : set A :=
  fun x => exists n : nat, E n x.

Definition same_set {A : Type} (E F : set A) : Prop :=
  forall x : A, E x <-> F x.

Definition subset {A : Type} (E F : set A) : Prop :=
  forall x : A, E x -> F x.

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

Definition ennreal_le
    (x y : extended_nonnegative) : Prop :=
  match x, y with
  | ennreal_finite a _, ennreal_finite b _ => a <= b
  | ennreal_finite _ _, ennreal_infinity => True
  | ennreal_infinity, ennreal_finite _ _ => False
  | ennreal_infinity, ennreal_infinity => True
  end.

Definition ennreal_positive (x : extended_nonnegative) : Prop :=
  match x with
  | ennreal_finite value _ => 0 < value
  | ennreal_infinity => True
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
          ennreal_mul
            (ennreal_of_nonnegative (coefficients i))
            (measure mu (cells i)))
        n.

Definition lintegral_has_value {A : Type}
    (mu : measure_space A)
    (f : A -> extended_nonnegative)
    (value : extended_nonnegative) : Prop :=
  ennreal_supremum (simple_integral_below mu f) value.

Definition real_indicator {A : Type}
    (E : set A) (f : A -> R) (x : A) : R :=
  if excluded_middle_informative (E x) then f x else 0.

Definition absolute_ennreal (x : R) : extended_nonnegative :=
  ennreal_finite (Rabs x) (Rabs_pos x).

Definition positive_part (x : R) : R :=
  Rmax x 0.

Definition negative_part (x : R) : R :=
  Rmax (- x) 0.

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

Definition integrable_on {A : Type}
    (mu : measure_space A) (E : set A) (f : A -> R) : Prop :=
  integrable mu (real_indicator E f).

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

Definition set_integral_has_value {A : Type}
    (mu : measure_space A) (E : set A)
    (f : A -> R) (value : R) : Prop :=
  lebesgue_integral_has_value mu (real_indicator E f) value.

Definition closed_unit_interval : set R :=
  fun x => 0 <= x <= 1.

Theorem putnam_1972_a6
    (mu : measure_space R)
    (hmu : is_lebesgue_measure mu)
    (f : R -> R)
    (n : nat)
    (hfintegrable : integrable_on mu closed_unit_interval f)
    (hfint :
      forall i : nat,
        (i < n)%nat ->
        set_integral_has_value mu closed_unit_interval
          (fun x : R => x ^ i * f x) 0)
    (hfintlast :
      set_integral_has_value mu closed_unit_interval
        (fun x : R => x ^ n * f x) 1) :
  exists S : set R,
    subset S closed_unit_interval /\
    measurable mu S /\
    ennreal_positive (measure mu S) /\
    forall x : R,
      S x ->
      Rabs (f x) >= 2 ^ n * (INR n + 1).
Admitted.
