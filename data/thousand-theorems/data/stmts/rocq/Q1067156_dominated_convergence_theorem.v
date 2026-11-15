(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1067156
  (thousand-theorems__rocq__Q1067156), "Dominated convergence theorem":
  almost-everywhere convergence of a sequence of strongly measurable
  normed-real-vector-space-valued functions dominated by an integrable real
  function implies convergence of their Bochner integrals. This file contains
  no proof.
*)

From Stdlib Require Import Reals ClassicalDescription.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1067156_set (A : Type) : Type := A -> Prop.

Definition q1067156_empty {A : Type} : q1067156_set A :=
  fun _ => False.

Definition q1067156_complement {A : Type}
    (E : q1067156_set A) : q1067156_set A :=
  fun x => ~ E x.

Definition q1067156_countable_union {A : Type}
    (E : nat -> q1067156_set A) : q1067156_set A :=
  fun x => exists n : nat, E n x.

Definition q1067156_same_set {A : Type}
    (E F : q1067156_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q1067156_disjoint {A : Type}
    (E F : q1067156_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q1067156_pairwise_disjoint {A : Type}
    (E : nat -> q1067156_set A) : Prop :=
  forall i j : nat, i <> j -> q1067156_disjoint (E i) (E j).

Inductive q1067156_ennreal : Type :=
| q1067156_ennreal_finite :
    forall value : R, 0 <= value -> q1067156_ennreal
| q1067156_ennreal_infinity : q1067156_ennreal.

Arguments q1067156_ennreal_finite value nonnegative : clear implicits.

Definition q1067156_ennreal_zero : q1067156_ennreal :=
  q1067156_ennreal_finite 0 (Rle_refl 0).

Definition q1067156_ennreal_le
    (x y : q1067156_ennreal) : Prop :=
  match x, y with
  | q1067156_ennreal_finite a _, q1067156_ennreal_finite b _ => a <= b
  | q1067156_ennreal_finite _ _, q1067156_ennreal_infinity => True
  | q1067156_ennreal_infinity, q1067156_ennreal_finite _ _ => False
  | q1067156_ennreal_infinity, q1067156_ennreal_infinity => True
  end.

Definition q1067156_ennreal_add
    (x y : q1067156_ennreal) : q1067156_ennreal :=
  match x, y with
  | q1067156_ennreal_finite a ha,
    q1067156_ennreal_finite b hb =>
      q1067156_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1067156_ennreal_infinity
  end.

Definition q1067156_ennreal_mul
    (x y : q1067156_ennreal) : q1067156_ennreal :=
  match x, y with
  | q1067156_ennreal_finite a ha,
    q1067156_ennreal_finite b hb =>
      q1067156_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q1067156_ennreal_finite a _, q1067156_ennreal_infinity
  | q1067156_ennreal_infinity, q1067156_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q1067156_ennreal_zero
      else q1067156_ennreal_infinity
  | q1067156_ennreal_infinity, q1067156_ennreal_infinity =>
      q1067156_ennreal_infinity
  end.

Fixpoint q1067156_ennreal_partial_sum
    (u : nat -> q1067156_ennreal) (n : nat) : q1067156_ennreal :=
  match n with
  | O => q1067156_ennreal_zero
  | S k =>
      q1067156_ennreal_add
        (q1067156_ennreal_partial_sum u k) (u k)
  end.

Definition q1067156_ennreal_supremum
    (values : q1067156_ennreal -> Prop)
    (bound : q1067156_ennreal) : Prop :=
  (forall value : q1067156_ennreal,
      values value -> q1067156_ennreal_le value bound) /\
  (forall upper : q1067156_ennreal,
      (forall value : q1067156_ennreal,
        values value -> q1067156_ennreal_le value upper) ->
      q1067156_ennreal_le bound upper).

Definition q1067156_ennreal_series_sum
    (u : nat -> q1067156_ennreal)
    (sum : q1067156_ennreal) : Prop :=
  q1067156_ennreal_supremum
    (fun value =>
      exists n : nat,
        value = q1067156_ennreal_partial_sum u n)
    sum.

Definition q1067156_ennreal_represents
    (x : q1067156_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    x = q1067156_ennreal_finite value nonnegative.

Definition q1067156_ennreal_finite_value
    (x : q1067156_ennreal) : Prop :=
  exists value : R, q1067156_ennreal_represents x value.

Record q1067156_measure_space (A : Type) : Type := {
  q1067156_measurable : q1067156_set A -> Prop;
  q1067156_measurable_extensional :
    forall E F : q1067156_set A,
      q1067156_same_set E F ->
      (q1067156_measurable E <-> q1067156_measurable F);
  q1067156_measurable_empty :
    q1067156_measurable q1067156_empty;
  q1067156_measurable_complement :
    forall E : q1067156_set A,
      q1067156_measurable E ->
      q1067156_measurable (q1067156_complement E);
  q1067156_measurable_countable_union :
    forall E : nat -> q1067156_set A,
      (forall n : nat, q1067156_measurable (E n)) ->
      q1067156_measurable (q1067156_countable_union E);
  q1067156_measure : q1067156_set A -> q1067156_ennreal;
  q1067156_measure_extensional :
    forall E F : q1067156_set A,
      q1067156_same_set E F ->
      q1067156_measure E = q1067156_measure F;
  q1067156_measure_empty :
    q1067156_measure q1067156_empty = q1067156_ennreal_zero;
  q1067156_measure_countable_additive :
    forall E : nat -> q1067156_set A,
      (forall n : nat, q1067156_measurable (E n)) ->
      q1067156_pairwise_disjoint E ->
      q1067156_ennreal_series_sum
        (fun n => q1067156_measure (E n))
        (q1067156_measure (q1067156_countable_union E))
}.

Arguments q1067156_measurable {A} _ _.
Arguments q1067156_measure {A} _ _.

Definition q1067156_almost_everywhere {A : Type}
    (mu : q1067156_measure_space A) (P : A -> Prop) : Prop :=
  exists null_set : q1067156_set A,
    q1067156_measurable mu null_set /\
    q1067156_measure mu null_set = q1067156_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q1067156_normed_real_vector_space (G : Type) : Type := {
  q1067156_zero : G;
  q1067156_add : G -> G -> G;
  q1067156_neg : G -> G;
  q1067156_smul : R -> G -> G;
  q1067156_norm : G -> R;
  q1067156_add_assoc :
    forall x y z : G,
      q1067156_add x (q1067156_add y z) =
      q1067156_add (q1067156_add x y) z;
  q1067156_add_comm :
    forall x y : G, q1067156_add x y = q1067156_add y x;
  q1067156_add_zero :
    forall x : G, q1067156_add x q1067156_zero = x;
  q1067156_add_neg :
    forall x : G, q1067156_add x (q1067156_neg x) = q1067156_zero;
  q1067156_one_smul :
    forall x : G, q1067156_smul 1 x = x;
  q1067156_mul_smul :
    forall (a b : R) (x : G),
      q1067156_smul (a * b) x =
      q1067156_smul a (q1067156_smul b x);
  q1067156_add_smul :
    forall (a b : R) (x : G),
      q1067156_smul (a + b) x =
      q1067156_add (q1067156_smul a x) (q1067156_smul b x);
  q1067156_smul_add :
    forall (a : R) (x y : G),
      q1067156_smul a (q1067156_add x y) =
      q1067156_add (q1067156_smul a x) (q1067156_smul a y);
  q1067156_zero_smul :
    forall x : G, q1067156_smul 0 x = q1067156_zero;
  q1067156_smul_zero :
    forall a : R, q1067156_smul a q1067156_zero = q1067156_zero;
  q1067156_norm_nonnegative :
    forall x : G, 0 <= q1067156_norm x;
  q1067156_norm_eq_zero :
    forall x : G, q1067156_norm x = 0 <-> x = q1067156_zero;
  q1067156_norm_add_le :
    forall x y : G,
      q1067156_norm (q1067156_add x y) <=
      q1067156_norm x + q1067156_norm y;
  q1067156_norm_smul :
    forall (a : R) (x : G),
      q1067156_norm (q1067156_smul a x) =
      Rabs a * q1067156_norm x
}.

Arguments q1067156_zero {G} _.
Arguments q1067156_add {G} _ _ _.
Arguments q1067156_neg {G} _ _.
Arguments q1067156_smul {G} _ _ _.
Arguments q1067156_norm {G} _ _.

Definition q1067156_sub {G : Type}
    (V : q1067156_normed_real_vector_space G)
    (x y : G) : G :=
  q1067156_add V x (q1067156_neg V y).

Definition q1067156_vector_sequence_converges {G : Type}
    (V : q1067156_normed_real_vector_space G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1067156_norm V (q1067156_sub V (u n) limit) < epsilon.

Definition q1067156_vector_sequence_cauchy {G : Type}
    (V : q1067156_normed_real_vector_space G)
    (u : nat -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q1067156_norm V (q1067156_sub V (u m) (u n)) < epsilon.

Definition q1067156_complete {G : Type}
    (V : q1067156_normed_real_vector_space G) : Prop :=
  forall u : nat -> G,
    q1067156_vector_sequence_cauchy V u ->
    exists limit : G, q1067156_vector_sequence_converges V u limit.

Definition q1067156_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q1067156_finite_partition {A : Type}
    (mu : q1067156_measure_space A)
    (k : nat) (cells : nat -> q1067156_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q1067156_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q1067156_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q1067156_measurable_simple {A G : Type}
    (mu : q1067156_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q1067156_set A),
    q1067156_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q1067156_measurable_simple_real {A : Type}
    (mu : q1067156_measure_space A)
    (s : A -> R) : Prop :=
  q1067156_measurable_simple mu s.

Definition q1067156_ae_strongly_measurable {A G : Type}
    (V : q1067156_normed_real_vector_space G)
    (mu : q1067156_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q1067156_measurable_simple mu (approximants n)) /\
    q1067156_almost_everywhere mu
      (fun x =>
        q1067156_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Definition q1067156_ae_strongly_measurable_real {A : Type}
    (mu : q1067156_measure_space A)
    (f : A -> R) : Prop :=
  exists approximants : nat -> A -> R,
    (forall n : nat,
      q1067156_measurable_simple_real mu (approximants n)) /\
    q1067156_almost_everywhere mu
      (fun x =>
        q1067156_real_sequence_converges
          (fun n => approximants n x) (f x)).

Record q1067156_nonnegative_real : Type := {
  q1067156_nnreal_value : R;
  q1067156_nnreal_nonnegative : 0 <= q1067156_nnreal_value
}.

Definition q1067156_ennreal_of_nonnegative
    (x : q1067156_nonnegative_real) : q1067156_ennreal :=
  q1067156_ennreal_finite
    (q1067156_nnreal_value x) (q1067156_nnreal_nonnegative x).

Definition q1067156_simple_lintegral_below {A : Type}
    (mu : q1067156_measure_space A)
    (f : A -> q1067156_ennreal)
    (value : q1067156_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q1067156_nonnegative_real)
         (cells : nat -> q1067156_set A),
    q1067156_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q1067156_ennreal_le
        (q1067156_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    value =
      q1067156_ennreal_partial_sum
        (fun i =>
          q1067156_ennreal_mul
            (q1067156_ennreal_of_nonnegative (coefficients i))
            (q1067156_measure mu (cells i)))
        k.

Definition q1067156_lintegral_has_value {A : Type}
    (mu : q1067156_measure_space A)
    (f : A -> q1067156_ennreal)
    (value : q1067156_ennreal) : Prop :=
  q1067156_ennreal_supremum
    (q1067156_simple_lintegral_below mu f) value.

Definition q1067156_absolute_ennreal (x : R) : q1067156_ennreal :=
  q1067156_ennreal_finite (Rabs x) (Rabs_pos x).

Definition q1067156_integrable_real {A : Type}
    (mu : q1067156_measure_space A)
    (f : A -> R) : Prop :=
  q1067156_ae_strongly_measurable_real mu f /\
  exists value : q1067156_ennreal,
    q1067156_lintegral_has_value mu
      (fun x => q1067156_absolute_ennreal (f x)) value /\
    q1067156_ennreal_finite_value value.

Fixpoint q1067156_vector_sum {G : Type}
    (V : q1067156_normed_real_vector_space G)
    (u : nat -> G) (n : nat) : G :=
  match n with
  | O => q1067156_zero V
  | S k =>
      q1067156_add V
        (q1067156_vector_sum V u k) (u k)
  end.

Definition q1067156_weighted_cell_value {A G : Type}
    (V : q1067156_normed_real_vector_space G)
    (mu : q1067156_measure_space A)
    (cell : q1067156_set A)
    (coefficient value : G) : Prop :=
  (coefficient = q1067156_zero V /\
    value = q1067156_zero V) \/
  exists mass : R,
    q1067156_ennreal_represents
      (q1067156_measure mu cell) mass /\
    value = q1067156_smul V mass coefficient.

Definition q1067156_simple_integral_has_value {A G : Type}
    (V : q1067156_normed_real_vector_space G)
    (mu : q1067156_measure_space A)
    (s : A -> G) (value : G) : Prop :=
  exists (k : nat) (coefficients terms : nat -> G)
         (cells : nat -> q1067156_set A),
    q1067156_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q1067156_weighted_cell_value
        V mu (cells i) (coefficients i) (terms i)) /\
    value = q1067156_vector_sum V terms k.

Definition q1067156_l1_approximates {A G : Type}
    (V : q1067156_normed_real_vector_space G)
    (mu : q1067156_measure_space A)
    (approximants : nat -> A -> G)
    (f : A -> G) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q1067156_ennreal,
        q1067156_lintegral_has_value mu
          (fun x =>
            q1067156_absolute_ennreal
              (q1067156_norm V
                (q1067156_sub V (approximants n x) (f x))))
          integral_error /\
        q1067156_ennreal_represents integral_error (errors n)) /\
    q1067156_real_sequence_converges errors 0.

Definition q1067156_standard_bochner_integral_value {A G : Type}
    (V : q1067156_normed_real_vector_space G)
    (mu : q1067156_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  exists (approximants : nat -> A -> G)
         (integrals : nat -> G),
    (forall n : nat,
      q1067156_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q1067156_simple_integral_has_value
        V mu (approximants n) (integrals n)) /\
    q1067156_l1_approximates V mu approximants f /\
    q1067156_vector_sequence_converges V integrals value.

Definition q1067156_bochner_integral_has_value {A G : Type}
    (V : q1067156_normed_real_vector_space G)
    (mu : q1067156_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  (~ q1067156_complete V /\ value = q1067156_zero V) \/
  (q1067156_complete V /\
    (q1067156_standard_bochner_integral_value V mu f value \/
     ((forall other : G,
        ~ q1067156_standard_bochner_integral_value V mu f other) /\
      value = q1067156_zero V))).

Theorem tendsto_integral_of_dominated_convergence :
  forall (Alpha G : Type)
         (V : q1067156_normed_real_vector_space G)
         (mu : q1067156_measure_space Alpha)
         (F : nat -> Alpha -> G)
         (f : Alpha -> G)
         (bound : Alpha -> R),
    (forall n : nat,
      q1067156_ae_strongly_measurable V mu (F n)) ->
    q1067156_integrable_real mu bound ->
    (forall n : nat,
      q1067156_almost_everywhere mu
        (fun a => q1067156_norm V (F n a) <= bound a)) ->
    q1067156_almost_everywhere mu
      (fun a =>
        q1067156_vector_sequence_converges V
          (fun n => F n a) (f a)) ->
    forall (integrals : nat -> G) (limit_integral : G),
      (forall n : nat,
        q1067156_bochner_integral_has_value
          V mu (F n) (integrals n)) ->
      q1067156_bochner_integral_has_value
        V mu f limit_integral ->
      q1067156_vector_sequence_converges
        V integrals limit_integral.
Admitted.
