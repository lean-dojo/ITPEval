(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1153584
  (thousand-theorems__rocq__Q1153584), "Monotone convergence theorem":
  almost-everywhere monotone convergence for extended-nonnegative Lebesgue
  integrals and antitone convergence for integrable real-valued Bochner
  integrals. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1153584_set (A : Type) : Type := A -> Prop.

Definition q1153584_empty {A : Type} : q1153584_set A :=
  fun _ => False.

Definition q1153584_complement {A : Type}
    (E : q1153584_set A) : q1153584_set A :=
  fun x => ~ E x.

Definition q1153584_countable_union {A : Type}
    (E : nat -> q1153584_set A) : q1153584_set A :=
  fun x => exists n : nat, E n x.

Definition q1153584_same_set {A : Type}
    (E F : q1153584_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1153584_disjoint {A : Type}
    (E F : q1153584_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1153584_pairwise_disjoint {A : Type}
    (E : nat -> q1153584_set A) : Prop :=
  forall i j : nat, i <> j -> q1153584_disjoint (E i) (E j).

Inductive q1153584_ennreal : Type :=
| q1153584_ennreal_finite :
    forall value : R, 0 <= value -> q1153584_ennreal
| q1153584_ennreal_infinity : q1153584_ennreal.

Arguments q1153584_ennreal_finite value nonnegative : clear implicits.

Definition q1153584_ennreal_zero : q1153584_ennreal :=
  q1153584_ennreal_finite 0 (Rle_refl 0).

Definition q1153584_ennreal_eq
    (x y : q1153584_ennreal) : Prop :=
  match x, y with
  | q1153584_ennreal_finite a _,
    q1153584_ennreal_finite b _ => a = b
  | q1153584_ennreal_infinity,
    q1153584_ennreal_infinity => True
  | _, _ => False
  end.

Definition q1153584_ennreal_le
    (x y : q1153584_ennreal) : Prop :=
  match x, y with
  | q1153584_ennreal_finite a _,
    q1153584_ennreal_finite b _ => a <= b
  | q1153584_ennreal_finite _ _,
    q1153584_ennreal_infinity => True
  | q1153584_ennreal_infinity,
    q1153584_ennreal_finite _ _ => False
  | q1153584_ennreal_infinity,
    q1153584_ennreal_infinity => True
  end.

Definition q1153584_ennreal_add
    (x y : q1153584_ennreal) : q1153584_ennreal :=
  match x, y with
  | q1153584_ennreal_finite a ha,
    q1153584_ennreal_finite b hb =>
      q1153584_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1153584_ennreal_infinity
  end.

Definition q1153584_ennreal_mul
    (x y : q1153584_ennreal) : q1153584_ennreal :=
  match x, y with
  | q1153584_ennreal_finite a ha,
    q1153584_ennreal_finite b hb =>
      q1153584_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q1153584_ennreal_finite a _, q1153584_ennreal_infinity
  | q1153584_ennreal_infinity, q1153584_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q1153584_ennreal_zero
      else q1153584_ennreal_infinity
  | q1153584_ennreal_infinity, q1153584_ennreal_infinity =>
      q1153584_ennreal_infinity
  end.

Fixpoint q1153584_ennreal_partial_sum
    (u : nat -> q1153584_ennreal)
    (n : nat) : q1153584_ennreal :=
  match n with
  | O => q1153584_ennreal_zero
  | S k =>
      q1153584_ennreal_add
        (q1153584_ennreal_partial_sum u k) (u k)
  end.

Definition q1153584_ennreal_supremum
    (values : q1153584_ennreal -> Prop)
    (bound : q1153584_ennreal) : Prop :=
  (forall value : q1153584_ennreal,
      values value -> q1153584_ennreal_le value bound) /\
  (forall upper : q1153584_ennreal,
      (forall value : q1153584_ennreal,
        values value -> q1153584_ennreal_le value upper) ->
      q1153584_ennreal_le bound upper).

Definition q1153584_ennreal_series_sum
    (u : nat -> q1153584_ennreal)
    (sum : q1153584_ennreal) : Prop :=
  q1153584_ennreal_supremum
    (fun value =>
      exists n : nat,
        q1153584_ennreal_eq value
          (q1153584_ennreal_partial_sum u n))
    sum.

Definition q1153584_ennreal_represents
    (x : q1153584_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q1153584_ennreal_eq x
      (q1153584_ennreal_finite value nonnegative).

Definition q1153584_ennreal_finite_value
    (x : q1153584_ennreal) : Prop :=
  exists value : R, q1153584_ennreal_represents x value.

Record q1153584_measure_space (A : Type) : Type := {
  q1153584_measurable : q1153584_set A -> Prop;
  q1153584_measurable_extensional :
    forall E F : q1153584_set A,
      q1153584_same_set E F ->
      (q1153584_measurable E <-> q1153584_measurable F);
  q1153584_measurable_empty :
    q1153584_measurable q1153584_empty;
  q1153584_measurable_complement :
    forall E : q1153584_set A,
      q1153584_measurable E ->
      q1153584_measurable (q1153584_complement E);
  q1153584_measurable_countable_union :
    forall E : nat -> q1153584_set A,
      (forall n : nat, q1153584_measurable (E n)) ->
      q1153584_measurable (q1153584_countable_union E);
  q1153584_measure : q1153584_set A -> q1153584_ennreal;
  q1153584_measure_extensional :
    forall E F : q1153584_set A,
      q1153584_same_set E F ->
      q1153584_ennreal_eq
        (q1153584_measure E) (q1153584_measure F);
  q1153584_measure_empty :
    q1153584_ennreal_eq
      (q1153584_measure q1153584_empty)
      q1153584_ennreal_zero;
  q1153584_measure_countable_additive :
    forall E : nat -> q1153584_set A,
      (forall n : nat, q1153584_measurable (E n)) ->
      q1153584_pairwise_disjoint E ->
      q1153584_ennreal_series_sum
        (fun n => q1153584_measure (E n))
        (q1153584_measure (q1153584_countable_union E))
}.

Arguments q1153584_measurable {A} _ _.
Arguments q1153584_measure {A} _ _.

Definition q1153584_almost_everywhere {A : Type}
    (mu : q1153584_measure_space A)
    (P : A -> Prop) : Prop :=
  exists null_set : q1153584_set A,
    q1153584_measurable mu null_set /\
    q1153584_ennreal_eq
      (q1153584_measure mu null_set)
      q1153584_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Definition q1153584_ennreal_below_real
    (x : q1153584_ennreal) (bound : R) : Prop :=
  match x with
  | q1153584_ennreal_finite value _ => value < bound
  | q1153584_ennreal_infinity => False
  end.

Definition q1153584_measurable_ennreal_function {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> q1153584_ennreal) : Prop :=
  forall bound : R,
    q1153584_measurable mu
      (fun x => q1153584_ennreal_below_real (f x) bound).

Definition q1153584_ae_measurable_ennreal_function {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> q1153584_ennreal) : Prop :=
  exists g : A -> q1153584_ennreal,
    q1153584_measurable_ennreal_function mu g /\
    q1153584_almost_everywhere mu
      (fun x => q1153584_ennreal_eq (f x) (g x)).

Definition q1153584_ennreal_above_real
    (x : q1153584_ennreal) (bound : R) : Prop :=
  match x with
  | q1153584_ennreal_finite value _ => bound < value
  | q1153584_ennreal_infinity => True
  end.

Definition q1153584_ennreal_sequence_converges
    (u : nat -> q1153584_ennreal)
    (limit : q1153584_ennreal) : Prop :=
  match limit with
  | q1153584_ennreal_finite value _ =>
      forall epsilon : R,
        0 < epsilon ->
        exists N : nat,
          forall n : nat,
            (N <= n)%nat ->
            match u n with
            | q1153584_ennreal_finite term _ =>
                Rabs (term - value) < epsilon
            | q1153584_ennreal_infinity => False
            end
  | q1153584_ennreal_infinity =>
      forall bound : R,
        exists N : nat,
          forall n : nat,
            (N <= n)%nat ->
            q1153584_ennreal_above_real (u n) bound
  end.

Definition q1153584_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q1153584_monotone_ennreal
    (u : nat -> q1153584_ennreal) : Prop :=
  forall n m : nat,
    (n <= m)%nat ->
    q1153584_ennreal_le (u n) (u m).

Definition q1153584_antitone_real
    (u : nat -> R) : Prop :=
  forall n m : nat,
    (n <= m)%nat ->
    u m <= u n.

Definition q1153584_finite_partition {A : Type}
    (mu : q1153584_measure_space A)
    (k : nat) (cells : nat -> q1153584_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q1153584_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q1153584_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q1153584_measurable_simple_real {A : Type}
    (mu : q1153584_measure_space A)
    (s : A -> R) : Prop :=
  exists (k : nat) (coefficients : nat -> R)
         (cells : nat -> q1153584_set A),
    q1153584_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q1153584_ae_strongly_measurable_real {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> R) : Prop :=
  exists approximants : nat -> A -> R,
    (forall n : nat,
      q1153584_measurable_simple_real mu (approximants n)) /\
    q1153584_almost_everywhere mu
      (fun x =>
        q1153584_real_sequence_converges
          (fun n => approximants n x) (f x)).

Record q1153584_nonnegative_real : Type := {
  q1153584_nnreal_value : R;
  q1153584_nnreal_nonnegative : 0 <= q1153584_nnreal_value
}.

Definition q1153584_ennreal_of_nonnegative
    (x : q1153584_nonnegative_real) : q1153584_ennreal :=
  q1153584_ennreal_finite
    (q1153584_nnreal_value x)
    (q1153584_nnreal_nonnegative x).

Definition q1153584_simple_lintegral_below {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> q1153584_ennreal)
    (value : q1153584_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q1153584_nonnegative_real)
         (cells : nat -> q1153584_set A),
    q1153584_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q1153584_ennreal_le
        (q1153584_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q1153584_ennreal_eq value
      (q1153584_ennreal_partial_sum
        (fun i =>
          q1153584_ennreal_mul
            (q1153584_ennreal_of_nonnegative (coefficients i))
            (q1153584_measure mu (cells i)))
        k).

Definition q1153584_lintegral_has_value {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> q1153584_ennreal)
    (value : q1153584_ennreal) : Prop :=
  q1153584_ennreal_supremum
    (q1153584_simple_lintegral_below mu f) value.

Definition q1153584_absolute_ennreal
    (x : R) : q1153584_ennreal :=
  q1153584_ennreal_finite (Rabs x) (Rabs_pos x).

Definition q1153584_positive_ennreal
    (x : R) : q1153584_ennreal :=
  q1153584_ennreal_finite (Rmax x 0) (Rmax_r x 0).

Definition q1153584_negative_ennreal
    (x : R) : q1153584_ennreal :=
  q1153584_ennreal_finite (Rmax (- x) 0) (Rmax_r (- x) 0).

Definition q1153584_integrable_real {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> R) : Prop :=
  q1153584_ae_strongly_measurable_real mu f /\
  exists value : q1153584_ennreal,
    q1153584_lintegral_has_value mu
      (fun x => q1153584_absolute_ennreal (f x)) value /\
    q1153584_ennreal_finite_value value.

Definition q1153584_bochner_integral_has_value {A : Type}
    (mu : q1153584_measure_space A)
    (f : A -> R) (value : R) : Prop :=
  exists (positive_integral negative_integral : q1153584_ennreal)
         (positive_value negative_value : R),
    q1153584_lintegral_has_value mu
      (fun x => q1153584_positive_ennreal (f x))
      positive_integral /\
    q1153584_lintegral_has_value mu
      (fun x => q1153584_negative_ennreal (f x))
      negative_integral /\
    q1153584_ennreal_represents
      positive_integral positive_value /\
    q1153584_ennreal_represents
      negative_integral negative_value /\
    value = positive_value - negative_value.

Theorem lintegral_tendsto_of_tendsto_of_monotone :
  forall (Alpha : Type)
         (mu : q1153584_measure_space Alpha)
         (f : nat -> Alpha -> q1153584_ennreal)
         (F : Alpha -> q1153584_ennreal),
    (forall n : nat,
      q1153584_ae_measurable_ennreal_function mu (f n)) ->
    q1153584_almost_everywhere mu
      (fun x => q1153584_monotone_ennreal (fun n => f n x)) ->
    q1153584_almost_everywhere mu
      (fun x =>
        q1153584_ennreal_sequence_converges
          (fun n => f n x) (F x)) ->
    exists (integrals : nat -> q1153584_ennreal)
           (limit_integral : q1153584_ennreal),
      (forall n : nat,
        q1153584_lintegral_has_value
          mu (f n) (integrals n)) /\
      q1153584_lintegral_has_value mu F limit_integral /\
      q1153584_ennreal_sequence_converges
        integrals limit_integral.
Admitted.

Theorem integral_tendsto_of_tendsto_of_antitone :
  forall (Alpha : Type)
         (mu : q1153584_measure_space Alpha)
         (f : nat -> Alpha -> R)
         (F : Alpha -> R),
    (forall n : nat, q1153584_integrable_real mu (f n)) ->
    q1153584_integrable_real mu F ->
    q1153584_almost_everywhere mu
      (fun x => q1153584_antitone_real (fun n => f n x)) ->
    q1153584_almost_everywhere mu
      (fun x =>
        q1153584_real_sequence_converges
          (fun n => f n x) (F x)) ->
    exists (integrals : nat -> R) (limit_integral : R),
      (forall n : nat,
        q1153584_bochner_integral_has_value
          mu (f n) (integrals n)) /\
      q1153584_bochner_integral_has_value
        mu F limit_integral /\
      q1153584_real_sequence_converges
        integrals limit_integral.
Admitted.
