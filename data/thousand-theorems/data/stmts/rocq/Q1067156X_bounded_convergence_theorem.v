(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1067156X
  (thousand-theorems__rocq__Q1067156X), "Bounded convergence theorem":
  uniformly bounded continuous nonnegative functions converging almost
  everywhere along a countably generated filter have convergent lower
  Lebesgue integrals, with the pointwise sequence specialization included.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1067156x_set (A : Type) : Type := A -> Prop.

Definition q1067156x_empty {A : Type} : q1067156x_set A :=
  fun _ => False.

Definition q1067156x_full {A : Type} : q1067156x_set A :=
  fun _ => True.

Definition q1067156x_complement {A : Type}
    (E : q1067156x_set A) : q1067156x_set A :=
  fun x => ~ E x.

Definition q1067156x_countable_union {A : Type}
    (E : nat -> q1067156x_set A) : q1067156x_set A :=
  fun x => exists n : nat, E n x.

Definition q1067156x_same_set {A : Type}
    (E F : q1067156x_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1067156x_subset {A : Type}
    (E F : q1067156x_set A) : Prop :=
  forall x : A, E x -> F x.

Definition q1067156x_disjoint {A : Type}
    (E F : q1067156x_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1067156x_pairwise_disjoint {A : Type}
    (E : nat -> q1067156x_set A) : Prop :=
  forall i j : nat, i <> j -> q1067156x_disjoint (E i) (E j).

Record q1067156x_topological_space (A : Type) : Type := {
  q1067156x_is_open : q1067156x_set A -> Prop;
  q1067156x_open_extensional :
    forall U V : q1067156x_set A,
      q1067156x_same_set U V ->
      (q1067156x_is_open U <-> q1067156x_is_open V);
  q1067156x_open_full :
    q1067156x_is_open q1067156x_full;
  q1067156x_open_intersection :
    forall U V : q1067156x_set A,
      q1067156x_is_open U ->
      q1067156x_is_open V ->
      q1067156x_is_open (fun x => U x /\ V x);
  q1067156x_open_union :
    forall family : q1067156x_set (q1067156x_set A),
      (forall U : q1067156x_set A,
        family U -> q1067156x_is_open U) ->
      q1067156x_is_open
        (fun x => exists U : q1067156x_set A, family U /\ U x)
}.

Arguments q1067156x_is_open {A} _ _.

Record q1067156x_measurable_space (A : Type) : Type := {
  q1067156x_measurable : q1067156x_set A -> Prop;
  q1067156x_measurable_extensional :
    forall E F : q1067156x_set A,
      q1067156x_same_set E F ->
      (q1067156x_measurable E <-> q1067156x_measurable F);
  q1067156x_measurable_empty :
    q1067156x_measurable q1067156x_empty;
  q1067156x_measurable_complement :
    forall E : q1067156x_set A,
      q1067156x_measurable E ->
      q1067156x_measurable (q1067156x_complement E);
  q1067156x_measurable_countable_union :
    forall E : nat -> q1067156x_set A,
      (forall n : nat, q1067156x_measurable (E n)) ->
      q1067156x_measurable (q1067156x_countable_union E)
}.

Arguments q1067156x_measurable {A} _ _.

Definition q1067156x_opens_measurable {A : Type}
    (T : q1067156x_topological_space A)
    (M : q1067156x_measurable_space A) : Prop :=
  forall U : q1067156x_set A,
    q1067156x_is_open T U -> q1067156x_measurable M U.

Record q1067156x_nnreal : Type := {
  q1067156x_nnreal_value : R;
  q1067156x_nnreal_nonnegative : 0 <= q1067156x_nnreal_value
}.

Definition q1067156x_nnreal_le
    (x y : q1067156x_nnreal) : Prop :=
  q1067156x_nnreal_value x <= q1067156x_nnreal_value y.

Definition q1067156x_nnreal_open
    (U : q1067156x_set q1067156x_nnreal) : Prop :=
  forall x : q1067156x_nnreal,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : q1067156x_nnreal,
        Rabs
          (q1067156x_nnreal_value y -
           q1067156x_nnreal_value x) < epsilon ->
        U y.

Definition q1067156x_continuous_nnreal {A : Type}
    (T : q1067156x_topological_space A)
    (f : A -> q1067156x_nnreal) : Prop :=
  forall U : q1067156x_set q1067156x_nnreal,
    q1067156x_nnreal_open U ->
    q1067156x_is_open T (fun x => U (f x)).

Record q1067156x_bounded_continuous_nnreal
    (A : Type) (T : q1067156x_topological_space A) : Type := {
  q1067156x_bc_apply : A -> q1067156x_nnreal;
  q1067156x_bc_continuous :
    q1067156x_continuous_nnreal T q1067156x_bc_apply;
  q1067156x_bc_bounded :
    exists bound : q1067156x_nnreal,
      forall x : A,
        q1067156x_nnreal_le (q1067156x_bc_apply x) bound
}.

Arguments q1067156x_bc_apply {A T} _ _.

Inductive q1067156x_ennreal : Type :=
| q1067156x_ennreal_finite :
    forall value : R, 0 <= value -> q1067156x_ennreal
| q1067156x_ennreal_infinity : q1067156x_ennreal.

Arguments q1067156x_ennreal_finite value nonnegative : clear implicits.

Definition q1067156x_ennreal_zero : q1067156x_ennreal :=
  q1067156x_ennreal_finite 0 (Rle_refl 0).

Definition q1067156x_ennreal_eq
    (x y : q1067156x_ennreal) : Prop :=
  match x, y with
  | q1067156x_ennreal_finite a _, q1067156x_ennreal_finite b _ =>
      a = b
  | q1067156x_ennreal_infinity, q1067156x_ennreal_infinity =>
      True
  | _, _ => False
  end.

Definition q1067156x_ennreal_le
    (x y : q1067156x_ennreal) : Prop :=
  match x, y with
  | q1067156x_ennreal_finite a _, q1067156x_ennreal_finite b _ =>
      a <= b
  | q1067156x_ennreal_finite _ _, q1067156x_ennreal_infinity =>
      True
  | q1067156x_ennreal_infinity, q1067156x_ennreal_finite _ _ =>
      False
  | q1067156x_ennreal_infinity, q1067156x_ennreal_infinity =>
      True
  end.

Definition q1067156x_ennreal_add
    (x y : q1067156x_ennreal) : q1067156x_ennreal :=
  match x, y with
  | q1067156x_ennreal_finite a ha,
    q1067156x_ennreal_finite b hb =>
      q1067156x_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1067156x_ennreal_infinity
  end.

Definition q1067156x_ennreal_mul
    (x y : q1067156x_ennreal) : q1067156x_ennreal :=
  match x, y with
  | q1067156x_ennreal_finite a ha,
    q1067156x_ennreal_finite b hb =>
      q1067156x_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q1067156x_ennreal_finite a _, q1067156x_ennreal_infinity
  | q1067156x_ennreal_infinity, q1067156x_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q1067156x_ennreal_zero
      else q1067156x_ennreal_infinity
  | q1067156x_ennreal_infinity, q1067156x_ennreal_infinity =>
      q1067156x_ennreal_infinity
  end.

Definition q1067156x_ennreal_of_nnreal
    (x : q1067156x_nnreal) : q1067156x_ennreal :=
  q1067156x_ennreal_finite
    (q1067156x_nnreal_value x) (q1067156x_nnreal_nonnegative x).

Definition q1067156x_ennreal_finite_value
    (x : q1067156x_ennreal) : Prop :=
  exists value : R,
    exists nonnegative : 0 <= value,
      q1067156x_ennreal_eq x
        (q1067156x_ennreal_finite value nonnegative).

Fixpoint q1067156x_ennreal_partial_sum
    (u : nat -> q1067156x_ennreal) (n : nat) : q1067156x_ennreal :=
  match n with
  | O => q1067156x_ennreal_zero
  | S k =>
      q1067156x_ennreal_add
        (q1067156x_ennreal_partial_sum u k) (u k)
  end.

Definition q1067156x_ennreal_supremum
    (values : q1067156x_ennreal -> Prop)
    (bound : q1067156x_ennreal) : Prop :=
  (forall value : q1067156x_ennreal,
      values value -> q1067156x_ennreal_le value bound) /\
  (forall upper : q1067156x_ennreal,
      (forall value : q1067156x_ennreal,
        values value -> q1067156x_ennreal_le value upper) ->
      q1067156x_ennreal_le bound upper).

Definition q1067156x_ennreal_series_sum
    (u : nat -> q1067156x_ennreal)
    (sum : q1067156x_ennreal) : Prop :=
  q1067156x_ennreal_supremum
    (fun value =>
      exists n : nat,
        q1067156x_ennreal_eq value
          (q1067156x_ennreal_partial_sum u n))
    sum.

Record q1067156x_measure {A : Type}
    (M : q1067156x_measurable_space A) : Type := {
  q1067156x_measure_value :
    q1067156x_set A -> q1067156x_ennreal;
  q1067156x_measure_extensional :
    forall E F : q1067156x_set A,
      q1067156x_same_set E F ->
      q1067156x_ennreal_eq
        (q1067156x_measure_value E)
        (q1067156x_measure_value F);
  q1067156x_measure_empty :
    q1067156x_ennreal_eq
      (q1067156x_measure_value q1067156x_empty)
      q1067156x_ennreal_zero;
  q1067156x_measure_countable_additive :
    forall E : nat -> q1067156x_set A,
      (forall n : nat, q1067156x_measurable M (E n)) ->
      q1067156x_pairwise_disjoint E ->
      q1067156x_ennreal_series_sum
        (fun n => q1067156x_measure_value (E n))
        (q1067156x_measure_value (q1067156x_countable_union E))
}.

Arguments q1067156x_measure_value {A M} _ _.

Definition q1067156x_finite_measure {A : Type}
    {M : q1067156x_measurable_space A}
    (mu : q1067156x_measure M) : Prop :=
  q1067156x_ennreal_finite_value
    (q1067156x_measure_value mu q1067156x_full).

Definition q1067156x_almost_everywhere {A : Type}
    {M : q1067156x_measurable_space A}
    (mu : q1067156x_measure M) (P : A -> Prop) : Prop :=
  exists null_set : q1067156x_set A,
    q1067156x_measurable M null_set /\
    q1067156x_ennreal_eq
      (q1067156x_measure_value mu null_set)
      q1067156x_ennreal_zero /\
    q1067156x_subset (fun x => ~ P x) null_set.

Definition q1067156x_finite_partition {A : Type}
    {M : q1067156x_measurable_space A}
    (mu : q1067156x_measure M)
    (k : nat) (cells : nat -> q1067156x_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q1067156x_measurable M (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q1067156x_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q1067156x_simple_lintegral_below {A : Type}
    {M : q1067156x_measurable_space A}
    (mu : q1067156x_measure M)
    (f : A -> q1067156x_ennreal)
    (value : q1067156x_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q1067156x_nnreal)
         (cells : nat -> q1067156x_set A),
    q1067156x_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q1067156x_ennreal_le
        (q1067156x_ennreal_of_nnreal (coefficients i))
        (f x)) /\
    q1067156x_ennreal_eq value
      (q1067156x_ennreal_partial_sum
        (fun i =>
          q1067156x_ennreal_mul
            (q1067156x_ennreal_of_nnreal (coefficients i))
            (q1067156x_measure_value mu (cells i)))
        k).

Definition q1067156x_lintegral_nnreal_has_value {A : Type}
    {M : q1067156x_measurable_space A}
    (mu : q1067156x_measure M)
    (f : A -> q1067156x_nnreal)
    (value : q1067156x_ennreal) : Prop :=
  q1067156x_ennreal_supremum
    (q1067156x_simple_lintegral_below mu
      (fun x => q1067156x_ennreal_of_nnreal (f x)))
    value.

Record q1067156x_filter (A : Type) : Type := {
  q1067156x_filter_sets : q1067156x_set A -> Prop;
  q1067156x_filter_full :
    q1067156x_filter_sets q1067156x_full;
  q1067156x_filter_superset :
    forall U V : q1067156x_set A,
      q1067156x_filter_sets U ->
      q1067156x_subset U V ->
      q1067156x_filter_sets V;
  q1067156x_filter_intersection :
    forall U V : q1067156x_set A,
      q1067156x_filter_sets U ->
      q1067156x_filter_sets V ->
      q1067156x_filter_sets (fun x => U x /\ V x)
}.

Arguments q1067156x_filter_sets {A} _ _.

Definition q1067156x_eventually {A : Type}
    (L : q1067156x_filter A) (P : A -> Prop) : Prop :=
  q1067156x_filter_sets L P.

Definition q1067156x_countably_generated {A : Type}
    (L : q1067156x_filter A) : Prop :=
  exists basis : nat -> q1067156x_set A,
    (forall n : nat, q1067156x_eventually L (basis n)) /\
    forall U : q1067156x_set A,
      q1067156x_eventually L U ->
      exists n : nat, q1067156x_subset (basis n) U.

Definition q1067156x_filter_tendsto_nnreal {A : Type}
    (u : A -> q1067156x_nnreal)
    (L : q1067156x_filter A)
    (limit : q1067156x_nnreal) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    q1067156x_eventually L
      (fun i =>
        Rabs
          (q1067156x_nnreal_value (u i) -
           q1067156x_nnreal_value limit) < epsilon).

Definition q1067156x_filter_tendsto_ennreal {A : Type}
    (u : A -> q1067156x_ennreal)
    (L : q1067156x_filter A)
    (limit : q1067156x_ennreal) : Prop :=
  match limit with
  | q1067156x_ennreal_finite value _ =>
      forall epsilon : R,
        0 < epsilon ->
        q1067156x_eventually L
          (fun i =>
            match u i with
            | q1067156x_ennreal_finite current _ =>
                Rabs (current - value) < epsilon
            | q1067156x_ennreal_infinity => False
            end)
  | q1067156x_ennreal_infinity =>
      forall threshold : R,
        q1067156x_eventually L
          (fun i =>
            match u i with
            | q1067156x_ennreal_finite current _ =>
                threshold < current
            | q1067156x_ennreal_infinity => True
            end)
  end.

Definition q1067156x_sequence_tendsto_nnreal
    (u : nat -> q1067156x_nnreal)
    (limit : q1067156x_nnreal) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs
          (q1067156x_nnreal_value (u n) -
           q1067156x_nnreal_value limit) < epsilon.

Definition q1067156x_sequence_tendsto_ennreal
    (u : nat -> q1067156x_ennreal)
    (limit : q1067156x_ennreal) : Prop :=
  match limit with
  | q1067156x_ennreal_finite value _ =>
      forall epsilon : R,
        0 < epsilon ->
        exists N : nat,
          forall n : nat,
            (N <= n)%nat ->
            match u n with
            | q1067156x_ennreal_finite current _ =>
                Rabs (current - value) < epsilon
            | q1067156x_ennreal_infinity => False
            end
  | q1067156x_ennreal_infinity =>
      forall threshold : R,
        exists N : nat,
          forall n : nat,
            (N <= n)%nat ->
            match u n with
            | q1067156x_ennreal_finite current _ =>
                threshold < current
            | q1067156x_ennreal_infinity => True
            end
  end.

Theorem tendsto_lintegral_nn_filter_of_le_const :
  forall (Omega Iota : Type)
         (T : q1067156x_topological_space Omega)
         (M : q1067156x_measurable_space Omega)
         (mu : q1067156x_measure M)
         (L : q1067156x_filter Iota)
         (fs :
           Iota -> q1067156x_bounded_continuous_nnreal T)
         (c : q1067156x_nnreal)
         (f : Omega -> q1067156x_nnreal),
    q1067156x_opens_measurable T M ->
    q1067156x_finite_measure mu ->
    q1067156x_countably_generated L ->
    q1067156x_eventually L
      (fun i =>
        q1067156x_almost_everywhere mu
          (fun omega =>
            q1067156x_nnreal_le
              (q1067156x_bc_apply (fs i) omega) c)) ->
    q1067156x_almost_everywhere mu
      (fun omega =>
        q1067156x_filter_tendsto_nnreal
          (fun i => q1067156x_bc_apply (fs i) omega)
          L (f omega)) ->
    exists (integrals : Iota -> q1067156x_ennreal)
           (limit_integral : q1067156x_ennreal),
      (forall i : Iota,
        q1067156x_lintegral_nnreal_has_value mu
          (fun omega => q1067156x_bc_apply (fs i) omega)
          (integrals i)) /\
      q1067156x_lintegral_nnreal_has_value mu f limit_integral /\
      q1067156x_filter_tendsto_ennreal
        integrals L limit_integral.
Admitted.

Theorem tendsto_lintegral_nn_of_le_const :
  forall (Omega : Type)
         (T : q1067156x_topological_space Omega)
         (M : q1067156x_measurable_space Omega)
         (mu : q1067156x_measure M)
         (fs :
           nat -> q1067156x_bounded_continuous_nnreal T)
         (c : q1067156x_nnreal)
         (f : Omega -> q1067156x_nnreal),
    q1067156x_opens_measurable T M ->
    q1067156x_finite_measure mu ->
    (forall (n : nat) (omega : Omega),
      q1067156x_nnreal_le
        (q1067156x_bc_apply (fs n) omega) c) ->
    (forall omega : Omega,
      q1067156x_sequence_tendsto_nnreal
        (fun n => q1067156x_bc_apply (fs n) omega)
        (f omega)) ->
    exists (integrals : nat -> q1067156x_ennreal)
           (limit_integral : q1067156x_ennreal),
      (forall n : nat,
        q1067156x_lintegral_nnreal_has_value mu
          (fun omega => q1067156x_bc_apply (fs n) omega)
          (integrals n)) /\
      q1067156x_lintegral_nnreal_has_value mu f limit_integral /\
      q1067156x_sequence_tendsto_ennreal
        integrals limit_integral.
Admitted.
