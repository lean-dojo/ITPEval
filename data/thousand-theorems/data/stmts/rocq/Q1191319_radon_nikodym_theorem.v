(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1191319
  (thousand-theorems__rocq__Q1191319), "Radon–Nikodym theorem":
  for two measures admitting a Lebesgue decomposition, absolute continuity is
  equivalent to recovering the first measure by weighting the second with its
  Radon–Nikodym derivative. This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1191319_set (A : Type) : Type := A -> Prop.

Definition q1191319_empty {A : Type} : q1191319_set A :=
  fun _ => False.

Definition q1191319_complement {A : Type}
    (E : q1191319_set A) : q1191319_set A :=
  fun x => ~ E x.

Definition q1191319_countable_union {A : Type}
    (E : nat -> q1191319_set A) : q1191319_set A :=
  fun x => exists n : nat, E n x.

Definition q1191319_same_set {A : Type}
    (E F : q1191319_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1191319_disjoint {A : Type}
    (E F : q1191319_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1191319_pairwise_disjoint {A : Type}
    (E : nat -> q1191319_set A) : Prop :=
  forall i j : nat, i <> j -> q1191319_disjoint (E i) (E j).

Inductive q1191319_ennreal : Type :=
| q1191319_ennreal_finite :
    forall value : R, 0 <= value -> q1191319_ennreal
| q1191319_ennreal_infinity : q1191319_ennreal.

Arguments q1191319_ennreal_finite value nonnegative : clear implicits.

Definition q1191319_ennreal_zero : q1191319_ennreal :=
  q1191319_ennreal_finite 0 (Rle_refl 0).

Definition q1191319_ennreal_eq
    (x y : q1191319_ennreal) : Prop :=
  match x, y with
  | q1191319_ennreal_finite a _,
    q1191319_ennreal_finite b _ => a = b
  | q1191319_ennreal_infinity,
    q1191319_ennreal_infinity => True
  | _, _ => False
  end.

Definition q1191319_ennreal_le
    (x y : q1191319_ennreal) : Prop :=
  match x, y with
  | q1191319_ennreal_finite a _,
    q1191319_ennreal_finite b _ => a <= b
  | q1191319_ennreal_finite _ _,
    q1191319_ennreal_infinity => True
  | q1191319_ennreal_infinity,
    q1191319_ennreal_finite _ _ => False
  | q1191319_ennreal_infinity,
    q1191319_ennreal_infinity => True
  end.

Definition q1191319_ennreal_add
    (x y : q1191319_ennreal) : q1191319_ennreal :=
  match x, y with
  | q1191319_ennreal_finite a ha,
    q1191319_ennreal_finite b hb =>
      q1191319_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1191319_ennreal_infinity
  end.

Definition q1191319_ennreal_mul
    (x y : q1191319_ennreal) : q1191319_ennreal :=
  match x, y with
  | q1191319_ennreal_finite a ha,
    q1191319_ennreal_finite b hb =>
      q1191319_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q1191319_ennreal_finite a _, q1191319_ennreal_infinity
  | q1191319_ennreal_infinity, q1191319_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q1191319_ennreal_zero
      else q1191319_ennreal_infinity
  | q1191319_ennreal_infinity, q1191319_ennreal_infinity =>
      q1191319_ennreal_infinity
  end.

Fixpoint q1191319_ennreal_partial_sum
    (u : nat -> q1191319_ennreal)
    (n : nat) : q1191319_ennreal :=
  match n with
  | O => q1191319_ennreal_zero
  | S k =>
      q1191319_ennreal_add
        (q1191319_ennreal_partial_sum u k) (u k)
  end.

Definition q1191319_ennreal_supremum
    (values : q1191319_ennreal -> Prop)
    (bound : q1191319_ennreal) : Prop :=
  (forall value : q1191319_ennreal,
      values value -> q1191319_ennreal_le value bound) /\
  (forall upper : q1191319_ennreal,
      (forall value : q1191319_ennreal,
        values value -> q1191319_ennreal_le value upper) ->
      q1191319_ennreal_le bound upper).

Definition q1191319_ennreal_series_sum
    (u : nat -> q1191319_ennreal)
    (sum : q1191319_ennreal) : Prop :=
  q1191319_ennreal_supremum
    (fun value =>
      exists n : nat,
        q1191319_ennreal_eq value
          (q1191319_ennreal_partial_sum u n))
    sum.

Record q1191319_measurable_space (A : Type) : Type := {
  q1191319_measurable : q1191319_set A -> Prop;
  q1191319_measurable_extensional :
    forall E F : q1191319_set A,
      q1191319_same_set E F ->
      (q1191319_measurable E <-> q1191319_measurable F);
  q1191319_measurable_empty :
    q1191319_measurable q1191319_empty;
  q1191319_measurable_complement :
    forall E : q1191319_set A,
      q1191319_measurable E ->
      q1191319_measurable (q1191319_complement E);
  q1191319_measurable_countable_union :
    forall E : nat -> q1191319_set A,
      (forall n : nat, q1191319_measurable (E n)) ->
      q1191319_measurable (q1191319_countable_union E)
}.

Arguments q1191319_measurable {A} _ _.

Record q1191319_measure (A : Type)
    (m : q1191319_measurable_space A) : Type := {
  q1191319_measure_value : q1191319_set A -> q1191319_ennreal;
  q1191319_measure_extensional :
    forall E F : q1191319_set A,
      q1191319_same_set E F ->
      q1191319_ennreal_eq
        (q1191319_measure_value E)
        (q1191319_measure_value F);
  q1191319_measure_empty :
    q1191319_ennreal_eq
      (q1191319_measure_value q1191319_empty)
      q1191319_ennreal_zero;
  q1191319_measure_monotone :
    forall E F : q1191319_set A,
      (forall x : A, E x -> F x) ->
      q1191319_ennreal_le
        (q1191319_measure_value E)
        (q1191319_measure_value F);
  q1191319_measure_trim :
    forall E : q1191319_set A,
      exists F : q1191319_set A,
        q1191319_measurable m F /\
        (forall x : A, E x -> F x) /\
        q1191319_ennreal_eq
          (q1191319_measure_value F)
          (q1191319_measure_value E);
  q1191319_measure_countable_subadditive :
    forall E : nat -> q1191319_set A,
      exists total : q1191319_ennreal,
        q1191319_ennreal_series_sum
          (fun n => q1191319_measure_value (E n)) total /\
        q1191319_ennreal_le
          (q1191319_measure_value (q1191319_countable_union E))
          total;
  q1191319_measure_countable_additive :
    forall E : nat -> q1191319_set A,
      (forall n : nat, q1191319_measurable m (E n)) ->
      q1191319_pairwise_disjoint E ->
      q1191319_ennreal_series_sum
        (fun n => q1191319_measure_value (E n))
        (q1191319_measure_value (q1191319_countable_union E))
}.

Arguments q1191319_measure_value {A m} _ _.

Definition q1191319_ennreal_below_real
    (x : q1191319_ennreal) (bound : R) : Prop :=
  match x with
  | q1191319_ennreal_finite value _ => value < bound
  | q1191319_ennreal_infinity => False
  end.

Definition q1191319_measurable_ennreal_function {A : Type}
    (m : q1191319_measurable_space A)
    (f : A -> q1191319_ennreal) : Prop :=
  forall bound : R,
    q1191319_measurable m
      (fun x => q1191319_ennreal_below_real (f x) bound).

Definition q1191319_finite_partition {A : Type}
    (m : q1191319_measurable_space A)
    (k : nat) (cells : nat -> q1191319_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q1191319_measurable m (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q1191319_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Record q1191319_nonnegative_real : Type := {
  q1191319_nnreal_value : R;
  q1191319_nnreal_nonnegative : 0 <= q1191319_nnreal_value
}.

Definition q1191319_ennreal_of_nonnegative
    (x : q1191319_nonnegative_real) : q1191319_ennreal :=
  q1191319_ennreal_finite
    (q1191319_nnreal_value x)
    (q1191319_nnreal_nonnegative x).

Definition q1191319_simple_lintegral_below {A : Type}
    {m : q1191319_measurable_space A}
    (mu : q1191319_measure m)
    (f : A -> q1191319_ennreal)
    (value : q1191319_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q1191319_nonnegative_real)
         (cells : nat -> q1191319_set A),
    q1191319_finite_partition m k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q1191319_ennreal_le
        (q1191319_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q1191319_ennreal_eq value
      (q1191319_ennreal_partial_sum
        (fun i =>
          q1191319_ennreal_mul
            (q1191319_ennreal_of_nonnegative (coefficients i))
            (q1191319_measure_value mu (cells i)))
        k).

Definition q1191319_lintegral_has_value {A : Type}
    {m : q1191319_measurable_space A}
    (mu : q1191319_measure m)
    (f : A -> q1191319_ennreal)
    (value : q1191319_ennreal) : Prop :=
  q1191319_ennreal_supremum
    (q1191319_simple_lintegral_below mu f) value.

Definition q1191319_indicator {A : Type}
    (E : q1191319_set A)
    (f : A -> q1191319_ennreal)
    (x : A) : q1191319_ennreal :=
  if excluded_middle_informative (E x)
  then f x
  else q1191319_ennreal_zero.

Definition q1191319_set_lintegral_has_value {A : Type}
    {m : q1191319_measurable_space A}
    (mu : q1191319_measure m)
    (E : q1191319_set A)
    (f : A -> q1191319_ennreal)
    (value : q1191319_ennreal) : Prop :=
  q1191319_lintegral_has_value mu
    (q1191319_indicator E f) value.

Definition q1191319_absolutely_continuous {A : Type}
    {m : q1191319_measurable_space A}
    (mu nu : q1191319_measure m) : Prop :=
  forall E : q1191319_set A,
    q1191319_ennreal_eq
      (q1191319_measure_value nu E)
      q1191319_ennreal_zero ->
    q1191319_ennreal_eq
      (q1191319_measure_value mu E)
      q1191319_ennreal_zero.

Definition q1191319_mutually_singular {A : Type}
    {m : q1191319_measurable_space A}
    (mu nu : q1191319_measure m) : Prop :=
  exists E : q1191319_set A,
    q1191319_measurable m E /\
    q1191319_ennreal_eq
      (q1191319_measure_value mu (q1191319_complement E))
      q1191319_ennreal_zero /\
    q1191319_ennreal_eq
      (q1191319_measure_value nu E)
      q1191319_ennreal_zero.

Definition q1191319_density_measure_equal {A : Type}
    {m : q1191319_measurable_space A}
    (nu : q1191319_measure m)
    (f : A -> q1191319_ennreal)
    (rho : q1191319_measure m) : Prop :=
  forall E : q1191319_set A,
    q1191319_measurable m E ->
    exists value : q1191319_ennreal,
      q1191319_set_lintegral_has_value nu E f value /\
      q1191319_ennreal_eq
        (q1191319_measure_value rho E) value.

Definition q1191319_lebesgue_decomposition {A : Type}
    {m : q1191319_measurable_space A}
    (mu singular nu : q1191319_measure m)
    (f : A -> q1191319_ennreal) : Prop :=
  forall E : q1191319_set A,
    q1191319_measurable m E ->
    exists density_value : q1191319_ennreal,
      q1191319_set_lintegral_has_value
        nu E f density_value /\
      q1191319_ennreal_eq
        (q1191319_measure_value mu E)
        (q1191319_ennreal_add
          (q1191319_measure_value singular E)
          density_value).

Definition q1191319_is_rn_deriv {A : Type}
    {m : q1191319_measurable_space A}
    (mu nu : q1191319_measure m)
    (f : A -> q1191319_ennreal) : Prop :=
  q1191319_measurable_ennreal_function m f /\
  exists singular : q1191319_measure m,
    q1191319_mutually_singular singular nu /\
    q1191319_lebesgue_decomposition mu singular nu f.

Definition q1191319_have_lebesgue_decomposition {A : Type}
    {m : q1191319_measurable_space A}
    (mu nu : q1191319_measure m) : Prop :=
  exists f : A -> q1191319_ennreal,
    q1191319_is_rn_deriv mu nu f.

Definition q1191319_rn_deriv {A : Type}
    {m : q1191319_measurable_space A}
    (mu nu : q1191319_measure m) : A -> q1191319_ennreal :=
  epsilon
    (inhabits (fun _ : A => q1191319_ennreal_zero))
    (q1191319_is_rn_deriv mu nu).

Theorem absolutelyContinuous_iff_withDensity_rnDeriv_eq :
  forall (Alpha : Type)
         (m : q1191319_measurable_space Alpha)
         (mu nu : q1191319_measure m),
    q1191319_have_lebesgue_decomposition mu nu ->
    (q1191319_absolutely_continuous mu nu <->
     q1191319_density_measure_equal
       nu (q1191319_rn_deriv mu nu) mu).
Admitted.
