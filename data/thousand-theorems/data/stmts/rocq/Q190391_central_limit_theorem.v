(*
  Statement-only formalization of Thousand Theorems corpus artifact Q190391
  (thousand-theorems__rocq__Q190391), "Central limit theorem": independent
  identically distributed real random variables with a finite second moment
  have centered sums, scaled by the inverse square root of the sample size,
  converging in distribution to the centered Gaussian with their variance.
  This file contains no proof.
*)

From Stdlib Require Import Reals RiemannInt List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q190391_set (A : Type) : Type := A -> Prop.

Definition q190391_empty {A : Type} : q190391_set A :=
  fun _ => False.

Definition q190391_full {A : Type} : q190391_set A :=
  fun _ => True.

Definition q190391_complement {A : Type}
    (E : q190391_set A) : q190391_set A :=
  fun x => ~ E x.

Definition q190391_countable_union {A : Type}
    (E : nat -> q190391_set A) : q190391_set A :=
  fun x => exists n : nat, E n x.

Definition q190391_preimage {A B : Type}
    (f : A -> B) (E : q190391_set B) : q190391_set A :=
  fun x => E (f x).

Definition q190391_same_set {A : Type}
    (E F : q190391_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q190391_disjoint {A : Type}
    (E F : q190391_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q190391_pairwise_disjoint {A : Type}
    (E : nat -> q190391_set A) : Prop :=
  forall i j : nat, i <> j -> q190391_disjoint (E i) (E j).

Fixpoint q190391_sum_first
    (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S k => q190391_sum_first k f + f k
  end.

Definition q190391_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q190391_series_sum
    (u : nat -> R) (sum : R) : Prop :=
  q190391_sequence_converges
    (fun n => q190391_sum_first n u) sum.

Definition q190391_sigma_class {A : Type}
    (C : q190391_set (q190391_set A)) : Prop :=
  C q190391_empty /\
  (forall E : q190391_set A,
    C E -> C (q190391_complement E)) /\
  (forall E : nat -> q190391_set A,
    (forall n : nat, C (E n)) ->
    C (q190391_countable_union E)).

Definition q190391_open_real_set
    (U : q190391_set R) : Prop :=
  forall x : R,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : R,
        Rabs (y - x) < epsilon ->
        U y.

Definition q190391_borel_set
    (E : q190391_set R) : Prop :=
  forall C : q190391_set (q190391_set R),
    q190391_sigma_class C ->
    (forall U : q190391_set R,
      q190391_open_real_set U -> C U) ->
    C E.

Record q190391_probability_space (A : Type) : Type := {
  q190391_measurable : q190391_set A -> Prop;
  q190391_measurable_extensional :
    forall E F : q190391_set A,
      q190391_same_set E F ->
      (q190391_measurable E <-> q190391_measurable F);
  q190391_measurable_empty :
    q190391_measurable q190391_empty;
  q190391_measurable_complement :
    forall E : q190391_set A,
      q190391_measurable E ->
      q190391_measurable (q190391_complement E);
  q190391_measurable_countable_union :
    forall E : nat -> q190391_set A,
      (forall n : nat, q190391_measurable (E n)) ->
      q190391_measurable (q190391_countable_union E);
  q190391_measure : q190391_set A -> R;
  q190391_measure_extensional :
    forall E F : q190391_set A,
      q190391_same_set E F ->
      q190391_measure E = q190391_measure F;
  q190391_measure_nonnegative :
    forall E : q190391_set A,
      q190391_measurable E ->
      0 <= q190391_measure E;
  q190391_measure_empty :
    q190391_measure q190391_empty = 0;
  q190391_measure_total :
    q190391_measure q190391_full = 1;
  q190391_measure_countable_additive :
    forall E : nat -> q190391_set A,
      (forall n : nat, q190391_measurable (E n)) ->
      q190391_pairwise_disjoint E ->
      q190391_series_sum
        (fun n => q190391_measure (E n))
        (q190391_measure (q190391_countable_union E))
}.

Arguments q190391_measurable {A} _ _.
Arguments q190391_measure {A} _ _.

Definition q190391_measurable_real_function {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) : Prop :=
  forall B : q190391_set R,
    q190391_borel_set B ->
    q190391_measurable P (q190391_preimage f B).

Definition q190391_almost_everywhere_equal {A : Type}
    (P : q190391_probability_space A)
    (f g : A -> R) : Prop :=
  exists null_set : q190391_set A,
    q190391_measurable P null_set /\
    q190391_measure P null_set = 0 /\
    forall x : A, ~ null_set x -> f x = g x.

Definition q190391_finite_partition {A : Type}
    (P : q190391_probability_space A)
    (k : nat) (cells : nat -> q190391_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q190391_measurable P (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q190391_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q190391_simple_integral_below {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) (value : R) : Prop :=
  exists (k : nat) (coefficients : nat -> R)
         (cells : nat -> q190391_set A),
    q190391_finite_partition P k cells /\
    (forall i : nat,
      (i < k)%nat -> 0 <= coefficients i) /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      coefficients i <= f x) /\
    value =
      q190391_sum_first k
        (fun i => coefficients i * q190391_measure P (cells i)).

Definition q190391_least_upper_bound
    (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> value <= bound) /\
  (forall upper : R,
    (forall value : R, values value -> value <= upper) ->
    bound <= upper).

Definition q190391_nonnegative_lebesgue_integral {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) (value : R) : Prop :=
  q190391_least_upper_bound
    (q190391_simple_integral_below P f) value.

Definition q190391_positive_part (x : R) : R :=
  Rmax x 0.

Definition q190391_negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition q190391_has_finite_lebesgue_integral {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) (value : R) : Prop :=
  q190391_measurable_real_function P f /\
  exists positive_integral negative_integral : R,
    q190391_nonnegative_lebesgue_integral P
      (fun x => q190391_positive_part (f x))
      positive_integral /\
    q190391_nonnegative_lebesgue_integral P
      (fun x => q190391_negative_part (f x))
      negative_integral /\
    value = positive_integral - negative_integral.

Definition q190391_has_expectation {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) (mean : R) : Prop :=
  exists representative : A -> R,
    q190391_almost_everywhere_equal P f representative /\
    q190391_has_finite_lebesgue_integral P representative mean.

Definition q190391_mem_L2 {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) : Prop :=
  exists (representative : A -> R) (second_moment : R),
    q190391_almost_everywhere_equal P f representative /\
    q190391_measurable_real_function P representative /\
    q190391_has_finite_lebesgue_integral P
      (fun x => (representative x) ^ 2) second_moment.

Definition q190391_has_mean_and_variance {A : Type}
    (P : q190391_probability_space A)
    (f : A -> R) (mean variance : R) : Prop :=
  q190391_has_expectation P f mean /\
  q190391_has_expectation P
    (fun x => (f x - mean) ^ 2) variance.

Fixpoint q190391_finite_intersection {A : Type}
    (X : nat -> A -> R) (indices : list nat)
    (events : nat -> q190391_set R) : q190391_set A :=
  match indices with
  | nil => q190391_full
  | i :: rest =>
      fun x =>
        events i (X i x) /\
        q190391_finite_intersection X rest events x
  end.

Fixpoint q190391_finite_product
    (indices : list nat) (f : nat -> R) : R :=
  match indices with
  | nil => 1
  | i :: rest => f i * q190391_finite_product rest f
  end.

Definition q190391_independent_random_variables {A : Type}
    (P : q190391_probability_space A)
    (X : nat -> A -> R) : Prop :=
  exists representative : nat -> A -> R,
    (forall n : nat,
      q190391_measurable_real_function P (representative n) /\
      q190391_almost_everywhere_equal P (X n) (representative n)) /\
    forall (indices : list nat)
           (events : nat -> q190391_set R),
      NoDup indices ->
      (forall i : nat,
        In i indices -> q190391_borel_set (events i)) ->
      q190391_measure P
        (q190391_finite_intersection representative indices events) =
      q190391_finite_product indices
        (fun i =>
          q190391_measure P
            (q190391_preimage (representative i) (events i))).

Definition q190391_identically_distributed {A : Type}
    (P : q190391_probability_space A)
    (f g : A -> R) : Prop :=
  exists f_representative g_representative : A -> R,
    q190391_measurable_real_function P f_representative /\
    q190391_measurable_real_function P g_representative /\
    q190391_almost_everywhere_equal P f f_representative /\
    q190391_almost_everywhere_equal P g g_representative /\
    forall B : q190391_set R,
      q190391_borel_set B ->
      q190391_measure P (q190391_preimage f_representative B) =
      q190391_measure P (q190391_preimage g_representative B).

Definition q190391_has_riemann_integral
    (f : R -> R) (a b value : R) : Prop :=
  exists integrable : Riemann_integrable f a b,
    @RiemannInt f a b integrable = value.

Definition q190391_tends_to_at_negative_infinity
    (f : R -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists cutoff : R,
      forall x : R,
        x <= cutoff ->
        Rabs (f x - limit) < epsilon.

Definition q190391_gaussian_density
    (mean variance x : R) : R :=
  exp (- ((x - mean) ^ 2) / (2 * variance)) /
  sqrt (2 * PI * variance).

Definition q190391_gaussian_cdf_value
    (mean variance t value : R) : Prop :=
  (variance = 0 /\
    value = if Rle_dec mean t then 1 else 0) \/
  (0 < variance /\
    exists finite_integral : R -> R,
      (forall a : R,
        q190391_has_riemann_integral
          (q190391_gaussian_density mean variance)
          a t (finite_integral a)) /\
      q190391_tends_to_at_negative_infinity
        finite_integral value).

Definition q190391_has_gaussian_law {A : Type}
    (P : q190391_probability_space A)
    (Y : A -> R) (mean variance : R) : Prop :=
  exists representative : A -> R,
    q190391_measurable_real_function P representative /\
    q190391_almost_everywhere_equal P Y representative /\
    forall t : R,
      exists value : R,
        q190391_gaussian_cdf_value mean variance t value /\
        q190391_measure P
          (fun x => representative x <= t) = value.

Definition q190391_continuous_at
    (f : R -> R) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        Rabs (y - x) < delta ->
        Rabs (f y - f x) < epsilon.

Definition q190391_tendsto_in_distribution {A B : Type}
    (P : q190391_probability_space A)
    (P' : q190391_probability_space B)
    (Z : nat -> A -> R) (Y : B -> R) : Prop :=
  exists (Z_representative : nat -> A -> R)
         (Y_representative : B -> R),
    (forall n : nat,
      q190391_measurable_real_function P (Z_representative n) /\
      q190391_almost_everywhere_equal P
        (Z n) (Z_representative n)) /\
    q190391_measurable_real_function P' Y_representative /\
    q190391_almost_everywhere_equal P' Y Y_representative /\
    forall t : R,
      q190391_continuous_at
        (fun s =>
          q190391_measure P'
            (fun x => Y_representative x <= s)) t ->
      q190391_sequence_converges
        (fun n =>
          q190391_measure P
            (fun x => Z_representative n x <= t))
        (q190391_measure P'
          (fun x => Y_representative x <= t)).

Theorem Q190391_canonical_statement :
  forall (Omega Omega' : Type)
         (P : q190391_probability_space Omega)
         (P' : q190391_probability_space Omega')
         (X : nat -> Omega -> R)
         (Y : Omega' -> R),
    q190391_mem_L2 P (X O) ->
    q190391_independent_random_variables P X ->
    (forall i : nat,
      q190391_identically_distributed P (X i) (X O)) ->
    forall mean variance : R,
      q190391_has_mean_and_variance P (X O) mean variance ->
      q190391_has_gaussian_law P' Y 0 variance ->
      q190391_tendsto_in_distribution P P'
        (fun (n : nat) (omega : Omega) =>
          / sqrt (INR n) *
          (q190391_sum_first n (fun k => X k omega) -
           INR n * mean))
        Y.
Admitted.
