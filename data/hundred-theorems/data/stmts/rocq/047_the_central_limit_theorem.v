(*
  Statement-only formalization of "The Central Limit Theorem" from Hundred
  Theorems item 047. It states the measure-theoretic central limit theorem for
  independent identically distributed real random variables, in zero-mean and
  centered forms, with convergence in distribution to the standard normal.
  This file contains no proof.
*)

From Stdlib Require Import Reals RiemannInt List.

Set Implicit Arguments.
Local Open Scope R_scope.

Definition set (A : Type) := A -> Prop.

Definition empty_set {A : Type} : set A :=
  fun _ => False.

Definition full_set {A : Type} : set A :=
  fun _ => True.

Definition set_complement {A : Type} (E : set A) : set A :=
  fun x => ~ E x.

Definition set_intersection {A : Type} (E F : set A) : set A :=
  fun x => E x /\ F x.

Definition countable_union {A : Type} (E : nat -> set A) : set A :=
  fun x => exists n : nat, E n x.

Definition preimage {A B : Type} (f : A -> B) (E : set B) : set A :=
  fun x => E (f x).

Definition same_set {A : Type} (E F : set A) : Prop :=
  forall x : A, E x <-> F x.

Definition disjoint_sets {A : Type} (E F : set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition pairwise_disjoint {A : Type} (E : nat -> set A) : Prop :=
  forall i j : nat, i <> j -> disjoint_sets (E i) (E j).

Fixpoint partial_sum (u : nat -> R) (n : nat) : R :=
  match n with
  | O => u O
  | S k => partial_sum u k + u (S k)
  end.

Definition sequence_converges (u : nat -> R) (limit : R) : Prop :=
  forall eps : R,
    0 < eps ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < eps.

Definition series_sum (u : nat -> R) (sum : R) : Prop :=
  sequence_converges (partial_sum u) sum.

Definition sigma_class {A : Type} (C : set (set A)) : Prop :=
  C empty_set /\
  (forall E : set A, C E -> C (set_complement E)) /\
  (forall E : nat -> set A,
      (forall n : nat, C (E n)) ->
      C (countable_union E)).

Definition open_real_set (U : set R) : Prop :=
  forall x : R,
    U x ->
    exists eps : R,
      0 < eps /\
      forall y : R, Rabs (y - x) < eps -> U y.

Definition borel_set (E : set R) : Prop :=
  forall C : set (set R),
    sigma_class C ->
    (forall U : set R, open_real_set U -> C U) ->
    C E.

Record probability_space (A : Type) := {
  ps_measurable : set A -> Prop;
  ps_measurable_empty : ps_measurable empty_set;
  ps_measurable_complement :
    forall E : set A,
      ps_measurable E ->
      ps_measurable (set_complement E);
  ps_measurable_countable_union :
    forall E : nat -> set A,
      (forall n : nat, ps_measurable (E n)) ->
      ps_measurable (countable_union E);
  ps_measure : set A -> R;
  ps_measure_extensional :
    forall E F : set A,
      same_set E F ->
      ps_measure E = ps_measure F;
  ps_measure_nonnegative :
    forall E : set A,
      ps_measurable E ->
      0 <= ps_measure E;
  ps_measure_empty : ps_measure empty_set = 0;
  ps_measure_total : ps_measure full_set = 1;
  ps_measure_countable_additive :
    forall E : nat -> set A,
      (forall n : nat, ps_measurable (E n)) ->
      pairwise_disjoint E ->
      series_sum
        (fun n => ps_measure (E n))
        (ps_measure (countable_union E))
}.

Record borel_measure := {
  bm_measure : set R -> R;
  bm_measure_extensional :
    forall E F : set R,
      same_set E F ->
      bm_measure E = bm_measure F;
  bm_measure_nonnegative :
    forall E : set R,
      borel_set E ->
      0 <= bm_measure E;
  bm_measure_empty : bm_measure empty_set = 0;
  bm_measure_countable_additive :
    forall E : nat -> set R,
      (forall n : nat, borel_set (E n)) ->
      pairwise_disjoint E ->
      series_sum
        (fun n => bm_measure (E n))
        (bm_measure (countable_union E))
}.

Definition measurable_real_function {A : Type}
    (measurable : set A -> Prop) (f : A -> R) : Prop :=
  forall B : set R,
    borel_set B ->
    measurable (preimage f B).

Definition finite_partition {A : Type}
    (measurable : set A -> Prop)
    (k : nat) (cells : nat -> set A) : Prop :=
  (forall i : nat, (i <= k)%nat -> measurable (cells i)) /\
  (forall i j : nat,
      (i <= k)%nat ->
      (j <= k)%nat ->
      i <> j ->
      disjoint_sets (cells i) (cells j)) /\
  (forall x : A,
      exists i : nat, (i <= k)%nat /\ cells i x).

Fixpoint finite_sum (k : nat) (f : nat -> R) : R :=
  match k with
  | O => f O
  | S n => finite_sum n f + f (S n)
  end.

Definition simple_integral_below {A : Type}
    (measurable : set A -> Prop) (measure : set A -> R)
    (f : A -> R) (value : R) : Prop :=
  exists (k : nat) (coefficients : nat -> R) (cells : nat -> set A),
    finite_partition measurable k cells /\
    (forall i : nat, (i <= k)%nat -> 0 <= coefficients i) /\
    (forall (x : A) (i : nat),
        (i <= k)%nat ->
        cells i x ->
        coefficients i <= f x) /\
    value =
      finite_sum k
        (fun i => coefficients i * measure (cells i)).

Definition least_upper_bound (values : R -> Prop) (bound : R) : Prop :=
  (forall value : R, values value -> value <= bound) /\
  (forall upper : R,
      (forall value : R, values value -> value <= upper) ->
      bound <= upper).

Definition nonnegative_lebesgue_integral {A : Type}
    (measurable : set A -> Prop) (measure : set A -> R)
    (f : A -> R) (value : R) : Prop :=
  least_upper_bound
    (simple_integral_below measurable measure f)
    value.

Definition positive_part (x : R) : R :=
  Rmax x 0.

Definition negative_part (x : R) : R :=
  Rmax (- x) 0.

Definition has_finite_lebesgue_integral {A : Type}
    (measurable : set A -> Prop) (measure : set A -> R)
    (f : A -> R) (value : R) : Prop :=
  measurable_real_function measurable f /\
  exists positive_integral negative_integral : R,
    nonnegative_lebesgue_integral measurable measure
      (fun x => positive_part (f x)) positive_integral /\
    nonnegative_lebesgue_integral measurable measure
      (fun x => negative_part (f x)) negative_integral /\
    value = positive_integral - negative_integral.

Definition random_variable {A : Type}
    (P : probability_space A) (X : A -> R) : Prop :=
  measurable_real_function (ps_measurable P) X.

Definition has_expectation {A : Type}
    (P : probability_space A) (X : A -> R) (mean : R) : Prop :=
  has_finite_lebesgue_integral
    (ps_measurable P) (ps_measure P) X mean.

Definition integrable {A : Type}
    (P : probability_space A) (X : A -> R) : Prop :=
  exists value : R, has_expectation P X value.

Definition square_integrable {A : Type}
    (P : probability_space A) (X : A -> R) : Prop :=
  integrable P (fun x => (X x) ^ 2).

Definition has_variance {A : Type}
    (P : probability_space A) (X : A -> R) (variance : R) : Prop :=
  exists mean : R,
    has_expectation P X mean /\
    has_expectation P (fun x => (X x - mean) ^ 2) variance.

Definition has_distribution {A : Type}
    (P : probability_space A) (X : A -> R)
    (mu : borel_measure) : Prop :=
  random_variable P X /\
  forall B : set R,
    borel_set B ->
    ps_measure P (preimage X B) = bm_measure mu B.

Fixpoint finite_intersection {A : Type}
    (X : nat -> A -> R) (indices : list nat)
    (events : nat -> set R) : set A :=
  match indices with
  | nil => full_set
  | i :: rest =>
      set_intersection
        (preimage (X i) (events i))
        (finite_intersection X rest events)
  end.

Fixpoint finite_product (indices : list nat) (f : nat -> R) : R :=
  match indices with
  | nil => 1
  | i :: rest => f i * finite_product rest f
  end.

Definition independent_random_variables {A : Type}
    (P : probability_space A) (X : nat -> A -> R) : Prop :=
  (forall n : nat, random_variable P (X n)) /\
  forall (indices : list nat) (events : nat -> set R),
    NoDup indices ->
    (forall i : nat, In i indices -> borel_set (events i)) ->
    ps_measure P (finite_intersection X indices events) =
    finite_product indices
      (fun i => ps_measure P (preimage (X i) (events i))).

Fixpoint sum_first (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S k => sum_first k f + f k
  end.

Definition has_riemann_integral
    (f : R -> R) (a b value : R) : Prop :=
  exists pr : Riemann_integrable f a b,
    @RiemannInt f a b pr = value.

Definition tends_to_at_negative_infinity
    (f : R -> R) (limit : R) : Prop :=
  forall eps : R,
    0 < eps ->
    exists cutoff : R,
      forall x : R,
        x <= cutoff ->
        Rabs (f x - limit) < eps.

Definition standard_normal_density (x : R) : R :=
  exp (- (x ^ 2) / 2) / sqrt (2 * PI).

Definition standard_normal_cdf_value (t value : R) : Prop :=
  exists finite_integral : R -> R,
    (forall a : R,
        has_riemann_integral
          standard_normal_density a t (finite_integral a)) /\
    tends_to_at_negative_infinity finite_integral value.

Definition converges_in_distribution_to_standard_normal {A : Type}
    (P : probability_space A) (Y : nat -> A -> R) : Prop :=
  (forall n : nat, random_variable P (Y n)) /\
  forall t : R,
    exists cdf_value : R,
      standard_normal_cdf_value t cdf_value /\
      sequence_converges
        (fun n =>
           ps_measure P (fun x => Y n x <= t))
        cdf_value.

Theorem central_limit_theorem_zero_mean :
  forall (A : Type) (P : probability_space A)
         (X : nat -> A -> R) (mu : borel_measure)
         (sigma : R) (S : nat -> A -> R),
    independent_random_variables P X ->
    (forall n : nat, has_expectation P (X n) 0) ->
    0 < sigma ->
    (forall n : nat, square_integrable P (X n)) ->
    (forall n : nat, has_variance P (X n) (sigma ^ 2)) ->
    (forall n : nat, has_distribution P (X n) mu) ->
    (forall (n : nat) (x : A),
        S n x = sum_first n (fun i => X i x)) ->
    converges_in_distribution_to_standard_normal P
      (fun n x =>
         S n x / sqrt (INR n * sigma ^ 2)).
Admitted.

Theorem central_limit_theorem :
  forall (A : Type) (P : probability_space A)
         (X : nat -> A -> R) (mu : borel_measure)
         (sigma : R) (S X_centered : nat -> A -> R) (m : R),
    independent_random_variables P X ->
    (forall n : nat, has_expectation P (X n) m) ->
    0 < sigma ->
    (forall n : nat, square_integrable P (X n)) ->
    (forall n : nat, has_variance P (X n) (sigma ^ 2)) ->
    (forall n : nat, has_distribution P (X n) mu) ->
    (forall (i : nat) (x : A),
        X_centered i x = X i x - m) ->
    converges_in_distribution_to_standard_normal P
      (fun n x =>
         sum_first n (fun i => X_centered i x) /
         sqrt (INR n * sigma ^ 2)).
Admitted.
