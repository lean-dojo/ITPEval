(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1217677
  (thousand-theorems__rocq__Q1217677), "Fundamental theorem of calculus":
  strict differentiation of a Lebesgue interval integral at an endpoint and
  recovery of a function from an integrable right derivative. This file
  contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1217677_set (A : Type) : Type := A -> Prop.

Definition q1217677_empty {A : Type} : q1217677_set A :=
  fun _ => False.

Definition q1217677_complement {A : Type}
    (S : q1217677_set A) : q1217677_set A :=
  fun x => ~ S x.

Definition q1217677_countable_union {A : Type}
    (S : nat -> q1217677_set A) : q1217677_set A :=
  fun x => exists n : nat, S n x.

Definition q1217677_same_set {A : Type}
    (S T : q1217677_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q1217677_disjoint {A : Type}
    (S T : q1217677_set A) : Prop :=
  forall x : A, ~ (S x /\ T x).

Definition q1217677_pairwise_disjoint {A : Type}
    (S : nat -> q1217677_set A) : Prop :=
  forall i j : nat, i <> j -> q1217677_disjoint (S i) (S j).

Definition q1217677_Ioc (a b : R) : q1217677_set R :=
  fun x => a < x /\ x <= b.

Definition q1217677_Icc (a b : R) : q1217677_set R :=
  fun x => a <= x /\ x <= b.

Definition q1217677_Ioo (a b : R) : q1217677_set R :=
  fun x => a < x /\ x < b.

Definition q1217677_Ioi (a : R) : q1217677_set R :=
  fun x => a < x.

Definition q1217677_open_interval (a b : R) : q1217677_set R :=
  q1217677_Ioo a b.

Definition q1217677_sigma_class
    (C : q1217677_set (q1217677_set R)) : Prop :=
  C q1217677_empty /\
  (forall S T : q1217677_set R,
    q1217677_same_set S T -> C S -> C T) /\
  (forall S : q1217677_set R,
    C S -> C (q1217677_complement S)) /\
  (forall S : nat -> q1217677_set R,
    (forall n : nat, C (S n)) ->
    C (q1217677_countable_union S)).

Inductive q1217677_ennreal : Type :=
| q1217677_ennreal_finite :
    forall value : R, 0 <= value -> q1217677_ennreal
| q1217677_ennreal_infinity : q1217677_ennreal.

Arguments q1217677_ennreal_finite value nonnegative : clear implicits.

Definition q1217677_ennreal_zero : q1217677_ennreal :=
  q1217677_ennreal_finite 0 (Rle_refl 0).

Definition q1217677_ennreal_eq
    (x y : q1217677_ennreal) : Prop :=
  match x, y with
  | q1217677_ennreal_finite a _,
    q1217677_ennreal_finite b _ => a = b
  | q1217677_ennreal_infinity,
    q1217677_ennreal_infinity => True
  | _, _ => False
  end.

Definition q1217677_ennreal_le
    (x y : q1217677_ennreal) : Prop :=
  match x, y with
  | q1217677_ennreal_finite a _,
    q1217677_ennreal_finite b _ => a <= b
  | q1217677_ennreal_finite _ _,
    q1217677_ennreal_infinity => True
  | q1217677_ennreal_infinity,
    q1217677_ennreal_finite _ _ => False
  | q1217677_ennreal_infinity,
    q1217677_ennreal_infinity => True
  end.

Definition q1217677_ennreal_add
    (x y : q1217677_ennreal) : q1217677_ennreal :=
  match x, y with
  | q1217677_ennreal_finite a ha,
    q1217677_ennreal_finite b hb =>
      q1217677_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q1217677_ennreal_infinity
  end.

Definition q1217677_ennreal_mul
    (x y : q1217677_ennreal) : q1217677_ennreal :=
  match x, y with
  | q1217677_ennreal_finite a ha,
    q1217677_ennreal_finite b hb =>
      q1217677_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q1217677_ennreal_finite a _, q1217677_ennreal_infinity
  | q1217677_ennreal_infinity, q1217677_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q1217677_ennreal_zero
      else q1217677_ennreal_infinity
  | q1217677_ennreal_infinity, q1217677_ennreal_infinity =>
      q1217677_ennreal_infinity
  end.

Fixpoint q1217677_ennreal_partial_sum
    (u : nat -> q1217677_ennreal)
    (n : nat) : q1217677_ennreal :=
  match n with
  | O => q1217677_ennreal_zero
  | S k =>
      q1217677_ennreal_add
        (q1217677_ennreal_partial_sum u k) (u k)
  end.

Definition q1217677_ennreal_supremum
    (values : q1217677_ennreal -> Prop)
    (bound : q1217677_ennreal) : Prop :=
  (forall value : q1217677_ennreal,
      values value -> q1217677_ennreal_le value bound) /\
  (forall upper : q1217677_ennreal,
      (forall value : q1217677_ennreal,
        values value -> q1217677_ennreal_le value upper) ->
      q1217677_ennreal_le bound upper).

Definition q1217677_ennreal_series_sum
    (u : nat -> q1217677_ennreal)
    (sum : q1217677_ennreal) : Prop :=
  q1217677_ennreal_supremum
    (fun value =>
      exists n : nat,
        q1217677_ennreal_eq value
          (q1217677_ennreal_partial_sum u n))
    sum.

Definition q1217677_ennreal_represents
    (x : q1217677_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q1217677_ennreal_eq x
      (q1217677_ennreal_finite value nonnegative).

Definition q1217677_ennreal_finite_value
    (x : q1217677_ennreal) : Prop :=
  exists value : R, q1217677_ennreal_represents x value.

Record q1217677_lebesgue_measure_space : Type := {
  q1217677_measurable : q1217677_set R -> Prop;
  q1217677_measurable_extensional :
    forall S T : q1217677_set R,
      q1217677_same_set S T ->
      (q1217677_measurable S <-> q1217677_measurable T);
  q1217677_measurable_empty :
    q1217677_measurable q1217677_empty;
  q1217677_measurable_complement :
    forall S : q1217677_set R,
      q1217677_measurable S ->
      q1217677_measurable (q1217677_complement S);
  q1217677_measurable_countable_union :
    forall S : nat -> q1217677_set R,
      (forall n : nat, q1217677_measurable (S n)) ->
      q1217677_measurable (q1217677_countable_union S);
  q1217677_measurable_open_interval :
    forall a b : R,
      q1217677_measurable (q1217677_open_interval a b);
  q1217677_measurable_borel_minimal :
    forall C : q1217677_set (q1217677_set R),
      q1217677_sigma_class C ->
      (forall a b : R, C (q1217677_open_interval a b)) ->
      forall S : q1217677_set R,
        q1217677_measurable S -> C S;
  q1217677_measure : q1217677_set R -> q1217677_ennreal;
  q1217677_measure_extensional :
    forall S T : q1217677_set R,
      q1217677_same_set S T ->
      q1217677_ennreal_eq
        (q1217677_measure S) (q1217677_measure T);
  q1217677_measure_empty :
    q1217677_ennreal_eq
      (q1217677_measure q1217677_empty)
      q1217677_ennreal_zero;
  q1217677_measure_monotone :
    forall S T : q1217677_set R,
      (forall x : R, S x -> T x) ->
      q1217677_ennreal_le
        (q1217677_measure S) (q1217677_measure T);
  q1217677_measure_trim :
    forall S : q1217677_set R,
      exists T : q1217677_set R,
        q1217677_measurable T /\
        (forall x : R, S x -> T x) /\
        q1217677_ennreal_eq
          (q1217677_measure T) (q1217677_measure S);
  q1217677_measure_countable_additive :
    forall S : nat -> q1217677_set R,
      (forall n : nat, q1217677_measurable (S n)) ->
      q1217677_pairwise_disjoint S ->
      q1217677_ennreal_series_sum
        (fun n => q1217677_measure (S n))
        (q1217677_measure (q1217677_countable_union S));
  q1217677_measure_Ioc :
    forall a b : R,
      q1217677_ennreal_eq
        (q1217677_measure (q1217677_Ioc a b))
        (q1217677_ennreal_finite
          (Rmax (b - a) 0) (Rmax_r (b - a) 0))
}.

Arguments q1217677_measurable _ _.
Arguments q1217677_measure _ _.

Definition q1217677_almost_everywhere
    (L : q1217677_lebesgue_measure_space)
    (P : R -> Prop) : Prop :=
  exists null_set : q1217677_set R,
    q1217677_ennreal_eq
      (q1217677_measure L null_set)
      q1217677_ennreal_zero /\
    forall x : R, ~ P x -> null_set x.

Record q1217677_normed_real_vector_space (E : Type) : Type := {
  q1217677_zero : E;
  q1217677_add : E -> E -> E;
  q1217677_neg : E -> E;
  q1217677_smul : R -> E -> E;
  q1217677_norm : E -> R;
  q1217677_add_assoc :
    forall x y z : E,
      q1217677_add x (q1217677_add y z) =
      q1217677_add (q1217677_add x y) z;
  q1217677_add_comm :
    forall x y : E, q1217677_add x y = q1217677_add y x;
  q1217677_add_zero :
    forall x : E, q1217677_add x q1217677_zero = x;
  q1217677_add_neg :
    forall x : E,
      q1217677_add x (q1217677_neg x) = q1217677_zero;
  q1217677_one_smul :
    forall x : E, q1217677_smul 1 x = x;
  q1217677_mul_smul :
    forall (a b : R) (x : E),
      q1217677_smul (a * b) x =
      q1217677_smul a (q1217677_smul b x);
  q1217677_add_smul :
    forall (a b : R) (x : E),
      q1217677_smul (a + b) x =
      q1217677_add (q1217677_smul a x) (q1217677_smul b x);
  q1217677_smul_add :
    forall (a : R) (x y : E),
      q1217677_smul a (q1217677_add x y) =
      q1217677_add (q1217677_smul a x) (q1217677_smul a y);
  q1217677_zero_smul :
    forall x : E, q1217677_smul 0 x = q1217677_zero;
  q1217677_smul_zero :
    forall a : R, q1217677_smul a q1217677_zero = q1217677_zero;
  q1217677_norm_nonnegative :
    forall x : E, 0 <= q1217677_norm x;
  q1217677_norm_eq_zero :
    forall x : E,
      q1217677_norm x = 0 <-> x = q1217677_zero;
  q1217677_norm_add_le :
    forall x y : E,
      q1217677_norm (q1217677_add x y) <=
      q1217677_norm x + q1217677_norm y;
  q1217677_norm_smul :
    forall (a : R) (x : E),
      q1217677_norm (q1217677_smul a x) =
      Rabs a * q1217677_norm x
}.

Arguments q1217677_zero {E} _.
Arguments q1217677_add {E} _ _ _.
Arguments q1217677_neg {E} _ _.
Arguments q1217677_smul {E} _ _ _.
Arguments q1217677_norm {E} _ _.

Definition q1217677_sub {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (x y : E) : E :=
  q1217677_add V x (q1217677_neg V y).

Definition q1217677_vector_sequence_converges {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1217677_norm V
          (q1217677_sub V (u n) limit) < epsilon.

Definition q1217677_vector_sequence_cauchy {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q1217677_norm V
          (q1217677_sub V (u m) (u n)) < epsilon.

Definition q1217677_complete {E : Type}
    (V : q1217677_normed_real_vector_space E) : Prop :=
  forall u : nat -> E,
    q1217677_vector_sequence_cauchy V u ->
    exists limit : E,
      q1217677_vector_sequence_converges V u limit.

Definition q1217677_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q1217677_finite_partition
    (L : q1217677_lebesgue_measure_space)
    (k : nat) (cells : nat -> q1217677_set R) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q1217677_measurable L (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q1217677_disjoint (cells i) (cells j)) /\
  (forall x : R,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q1217677_measurable_simple {E : Type}
    (L : q1217677_lebesgue_measure_space)
    (s : R -> E) : Prop :=
  exists (k : nat) (coefficients : nat -> E)
         (cells : nat -> q1217677_set R),
    q1217677_finite_partition L k cells /\
    forall (x : R) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q1217677_strongly_measurable_on {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (S : q1217677_set R) : Prop :=
  exists approximants : nat -> R -> E,
    (forall n : nat,
      q1217677_measurable_simple L (approximants n)) /\
    forall x : R,
      S x ->
      q1217677_vector_sequence_converges V
        (fun n => approximants n x) (f x).

Definition q1217677_ae_strongly_measurable {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) : Prop :=
  exists approximants : nat -> R -> E,
    (forall n : nat,
      q1217677_measurable_simple L (approximants n)) /\
    q1217677_almost_everywhere L
      (fun x =>
        q1217677_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q1217677_nonnegative_real : Type := {
  q1217677_nnreal_value : R;
  q1217677_nnreal_nonnegative : 0 <= q1217677_nnreal_value
}.

Definition q1217677_ennreal_of_nonnegative
    (x : q1217677_nonnegative_real) : q1217677_ennreal :=
  q1217677_ennreal_finite
    (q1217677_nnreal_value x)
    (q1217677_nnreal_nonnegative x).

Definition q1217677_simple_lintegral_below
    (L : q1217677_lebesgue_measure_space)
    (f : R -> q1217677_ennreal)
    (value : q1217677_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q1217677_nonnegative_real)
         (cells : nat -> q1217677_set R),
    q1217677_finite_partition L k cells /\
    (forall (x : R) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q1217677_ennreal_le
        (q1217677_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q1217677_ennreal_eq value
      (q1217677_ennreal_partial_sum
        (fun i =>
          q1217677_ennreal_mul
            (q1217677_ennreal_of_nonnegative (coefficients i))
            (q1217677_measure L (cells i)))
        k).

Definition q1217677_lintegral_has_value
    (L : q1217677_lebesgue_measure_space)
    (f : R -> q1217677_ennreal)
    (value : q1217677_ennreal) : Prop :=
  q1217677_ennreal_supremum
    (q1217677_simple_lintegral_below L f) value.

Definition q1217677_norm_ennreal {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (x : E) : q1217677_ennreal :=
  q1217677_ennreal_finite
    (q1217677_norm V x)
    (q1217677_norm_nonnegative V x).

Definition q1217677_indicator {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (S : q1217677_set R) (f : R -> E) (x : R) : E :=
  if excluded_middle_informative (S x)
  then f x
  else q1217677_zero V.

Definition q1217677_integrable {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) : Prop :=
  q1217677_ae_strongly_measurable V L f /\
  exists value : q1217677_ennreal,
    q1217677_lintegral_has_value L
      (fun x => q1217677_norm_ennreal V (f x)) value /\
    q1217677_ennreal_finite_value value.

Definition q1217677_integrable_on {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (S : q1217677_set R) : Prop :=
  q1217677_integrable V L (q1217677_indicator V S f).

Definition q1217677_interval_integrable {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (a b : R) : Prop :=
  q1217677_integrable_on V L f (q1217677_Ioc a b) /\
  q1217677_integrable_on V L f (q1217677_Ioc b a).

Fixpoint q1217677_vector_sum {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (u : nat -> E) (n : nat) : E :=
  match n with
  | O => q1217677_zero V
  | S k =>
      q1217677_add V
        (q1217677_vector_sum V u k) (u k)
  end.

Definition q1217677_weighted_cell_value {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (cell : q1217677_set R)
    (coefficient value : E) : Prop :=
  (coefficient = q1217677_zero V /\
    value = q1217677_zero V) \/
  exists mass : R,
    q1217677_ennreal_represents
      (q1217677_measure L cell) mass /\
    value = q1217677_smul V mass coefficient.

Definition q1217677_simple_integral_has_value {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (s : R -> E) (value : E) : Prop :=
  exists (k : nat) (coefficients terms : nat -> E)
         (cells : nat -> q1217677_set R),
    q1217677_finite_partition L k cells /\
    (forall (x : R) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q1217677_weighted_cell_value
        V L (cells i) (coefficients i) (terms i)) /\
    value = q1217677_vector_sum V terms k.

Definition q1217677_l1_approximates {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (approximants : nat -> R -> E)
    (f : R -> E) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q1217677_ennreal,
        q1217677_lintegral_has_value L
          (fun x =>
            q1217677_norm_ennreal V
              (q1217677_sub V (approximants n x) (f x)))
          integral_error /\
        q1217677_ennreal_represents
          integral_error (errors n)) /\
    q1217677_real_sequence_converges errors 0.

Definition q1217677_standard_bochner_integral_value {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (value : E) : Prop :=
  exists (approximants : nat -> R -> E)
         (integrals : nat -> E),
    (forall n : nat,
      q1217677_measurable_simple L (approximants n)) /\
    (forall n : nat,
      q1217677_simple_integral_has_value
        V L (approximants n) (integrals n)) /\
    q1217677_l1_approximates V L approximants f /\
    q1217677_vector_sequence_converges V integrals value.

Definition q1217677_bochner_integral {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) : E :=
  match excluded_middle_informative
          (exists value : E,
            q1217677_standard_bochner_integral_value V L f value) with
  | left _ =>
      epsilon (inhabits (q1217677_zero V))
        (fun value : E =>
          q1217677_standard_bochner_integral_value V L f value)
  | right _ => q1217677_zero V
  end.

Definition q1217677_interval_integral {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (a b : R) : E :=
  q1217677_sub V
    (q1217677_bochner_integral V L
      (q1217677_indicator V (q1217677_Ioc a b) f))
    (q1217677_bochner_integral V L
      (q1217677_indicator V (q1217677_Ioc b a) f)).

Definition q1217677_strongly_measurable_at {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (b : R) : Prop :=
  exists delta : R,
    0 < delta /\
    q1217677_ae_strongly_measurable V L
      (q1217677_indicator V
        (fun x => Rabs (x - b) < delta) f).

Definition q1217677_tendsto_ae_at {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (L : q1217677_lebesgue_measure_space)
    (f : R -> E) (b : R) (c : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists (delta : R) (null_set : q1217677_set R),
      0 < delta /\
      q1217677_ennreal_eq
        (q1217677_measure L null_set)
        q1217677_ennreal_zero /\
      forall x : R,
        Rabs (x - b) < delta ->
        ~ null_set x ->
        q1217677_norm V
          (q1217677_sub V (f x) c) < epsilon.

Definition q1217677_continuous_within_at {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (f : R -> E) (S : q1217677_set R) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        S y ->
        Rabs (y - x) < delta ->
        q1217677_norm V
          (q1217677_sub V (f y) (f x)) < epsilon.

Definition q1217677_continuous_on {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (f : R -> E) (S : q1217677_set R) : Prop :=
  forall x : R,
    S x ->
    q1217677_continuous_within_at V f S x.

Definition q1217677_has_deriv_within_at {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (f : R -> E) (derivative : E)
    (S : q1217677_set R) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        S y ->
        Rabs (y - x) < delta ->
        q1217677_norm V
          (q1217677_sub V
            (q1217677_sub V (f y) (f x))
            (q1217677_smul V (y - x) derivative))
        <= epsilon * Rabs (y - x).

Definition q1217677_has_strict_deriv_at {E : Type}
    (V : q1217677_normed_real_vector_space E)
    (f : R -> E) (derivative : E) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y z : R,
        Rabs (y - x) < delta ->
        Rabs (z - x) < delta ->
        q1217677_norm V
          (q1217677_sub V
            (q1217677_sub V (f y) (f z))
            (q1217677_smul V (y - z) derivative))
        <= epsilon * Rabs (y - z).

Theorem intervalIntegral_integral_hasStrictDerivAt_of_tendsto_ae_right :
  forall (E : Type)
         (V : q1217677_normed_real_vector_space E)
         (L : q1217677_lebesgue_measure_space)
         (f : R -> E) (a b : R) (c : E),
    q1217677_complete V ->
    q1217677_interval_integrable V L f a b ->
    q1217677_strongly_measurable_at V L f b ->
    q1217677_tendsto_ae_at V L f b c ->
    q1217677_has_strict_deriv_at V
      (fun u => q1217677_interval_integral V L f a u) c b.
Admitted.

Theorem intervalIntegral_integral_eq_sub_of_hasDeriv_right_of_le :
  forall (E : Type)
         (V : q1217677_normed_real_vector_space E)
         (L : q1217677_lebesgue_measure_space)
         (f f' : R -> E) (a b : R),
    q1217677_complete V ->
    a <= b ->
    q1217677_continuous_on V f (q1217677_Icc a b) ->
    (forall x : R,
      q1217677_Ioo a b x ->
      q1217677_has_deriv_within_at
        V f (f' x) (q1217677_Ioi x) x) ->
    q1217677_interval_integrable V L f' a b ->
    q1217677_interval_integral V L f' a b =
      q1217677_sub V (f b) (f a).
Admitted.
