(*
  Statement-only formalization of Thousand Theorems corpus artifact Q6813106
  (thousand-theorems__rocq__Q6813106), "Mellin inversion theorem": the
  inverse Mellin transform of the Mellin transform recovers a function at a
  positive real point under Mellin convergence, vertical integrability, and
  continuity at that point.
  This file contains no proof.
*)

From Stdlib Require Import Reals ClassicalDescription ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q6813106_set (A : Type) : Type := A -> Prop.

Definition q6813106_empty {A : Type} : q6813106_set A :=
  fun _ => False.

Definition q6813106_full {A : Type} : q6813106_set A :=
  fun _ => True.

Definition q6813106_complement {A : Type}
    (E : q6813106_set A) : q6813106_set A :=
  fun x => ~ E x.

Definition q6813106_countable_union {A : Type}
    (E : nat -> q6813106_set A) : q6813106_set A :=
  fun x => exists n : nat, E n x.

Definition q6813106_same_set {A : Type}
    (E F : q6813106_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q6813106_disjoint {A : Type}
    (E F : q6813106_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q6813106_pairwise_disjoint {A : Type}
    (E : nat -> q6813106_set A) : Prop :=
  forall i j : nat, i <> j -> q6813106_disjoint (E i) (E j).

Definition q6813106_sigma_class {A : Type}
    (C : q6813106_set (q6813106_set A)) : Prop :=
  C q6813106_empty /\
  (forall E F : q6813106_set A,
    q6813106_same_set E F ->
    C E ->
    C F) /\
  (forall E : q6813106_set A,
    C E -> C (q6813106_complement E)) /\
  (forall E : nat -> q6813106_set A,
    (forall n : nat, C (E n)) ->
    C (q6813106_countable_union E)).

Inductive q6813106_ennreal : Type :=
| q6813106_ennreal_finite :
    forall value : R, 0 <= value -> q6813106_ennreal
| q6813106_ennreal_infinity : q6813106_ennreal.

Arguments q6813106_ennreal_finite value nonnegative : clear implicits.

Definition q6813106_ennreal_zero : q6813106_ennreal :=
  q6813106_ennreal_finite 0 (Rle_refl 0).

Definition q6813106_ennreal_eq
    (x y : q6813106_ennreal) : Prop :=
  match x, y with
  | q6813106_ennreal_finite a _,
    q6813106_ennreal_finite b _ => a = b
  | q6813106_ennreal_infinity,
    q6813106_ennreal_infinity => True
  | _, _ => False
  end.

Definition q6813106_ennreal_le
    (x y : q6813106_ennreal) : Prop :=
  match x, y with
  | q6813106_ennreal_finite a _,
    q6813106_ennreal_finite b _ => a <= b
  | q6813106_ennreal_finite _ _,
    q6813106_ennreal_infinity => True
  | q6813106_ennreal_infinity,
    q6813106_ennreal_finite _ _ => False
  | q6813106_ennreal_infinity,
    q6813106_ennreal_infinity => True
  end.

Definition q6813106_ennreal_add
    (x y : q6813106_ennreal) : q6813106_ennreal :=
  match x, y with
  | q6813106_ennreal_finite a ha,
    q6813106_ennreal_finite b hb =>
      q6813106_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q6813106_ennreal_infinity
  end.

Definition q6813106_ennreal_mul
    (x y : q6813106_ennreal) : q6813106_ennreal :=
  match x, y with
  | q6813106_ennreal_finite a ha,
    q6813106_ennreal_finite b hb =>
      q6813106_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q6813106_ennreal_finite a _, q6813106_ennreal_infinity
  | q6813106_ennreal_infinity, q6813106_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q6813106_ennreal_zero
      else q6813106_ennreal_infinity
  | q6813106_ennreal_infinity, q6813106_ennreal_infinity =>
      q6813106_ennreal_infinity
  end.

Fixpoint q6813106_ennreal_partial_sum
    (u : nat -> q6813106_ennreal)
    (n : nat) : q6813106_ennreal :=
  match n with
  | O => q6813106_ennreal_zero
  | S k =>
      q6813106_ennreal_add
        (q6813106_ennreal_partial_sum u k) (u k)
  end.

Definition q6813106_ennreal_supremum
    (values : q6813106_ennreal -> Prop)
    (bound : q6813106_ennreal) : Prop :=
  (forall value : q6813106_ennreal,
      values value -> q6813106_ennreal_le value bound) /\
  (forall upper : q6813106_ennreal,
      (forall value : q6813106_ennreal,
        values value -> q6813106_ennreal_le value upper) ->
      q6813106_ennreal_le bound upper).

Definition q6813106_ennreal_series_sum
    (u : nat -> q6813106_ennreal)
    (sum : q6813106_ennreal) : Prop :=
  q6813106_ennreal_supremum
    (fun value =>
      exists n : nat,
        q6813106_ennreal_eq value
          (q6813106_ennreal_partial_sum u n))
    sum.

Definition q6813106_ennreal_represents
    (x : q6813106_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q6813106_ennreal_eq x
      (q6813106_ennreal_finite value nonnegative).

Definition q6813106_ennreal_finite_value
    (x : q6813106_ennreal) : Prop :=
  exists value : R, q6813106_ennreal_represents x value.

Record q6813106_measure_space (A : Type) : Type := {
  q6813106_measurable : q6813106_set A -> Prop;
  q6813106_measurable_extensional :
    forall E F : q6813106_set A,
      q6813106_same_set E F ->
      (q6813106_measurable E <-> q6813106_measurable F);
  q6813106_measurable_empty :
    q6813106_measurable q6813106_empty;
  q6813106_measurable_complement :
    forall E : q6813106_set A,
      q6813106_measurable E ->
      q6813106_measurable (q6813106_complement E);
  q6813106_measurable_countable_union :
    forall E : nat -> q6813106_set A,
      (forall n : nat, q6813106_measurable (E n)) ->
      q6813106_measurable (q6813106_countable_union E);
  q6813106_measure : q6813106_set A -> q6813106_ennreal;
  q6813106_measure_extensional :
    forall E F : q6813106_set A,
      q6813106_same_set E F ->
      q6813106_ennreal_eq
        (q6813106_measure E) (q6813106_measure F);
  q6813106_measure_empty :
    q6813106_ennreal_eq
      (q6813106_measure q6813106_empty)
      q6813106_ennreal_zero;
  q6813106_measure_countable_additive :
    forall E : nat -> q6813106_set A,
      (forall n : nat, q6813106_measurable (E n)) ->
      q6813106_pairwise_disjoint E ->
      q6813106_ennreal_series_sum
        (fun n => q6813106_measure (E n))
        (q6813106_measure (q6813106_countable_union E))
}.

Arguments q6813106_measurable {A} _ _.
Arguments q6813106_measure {A} _ _.

Definition q6813106_almost_everywhere {A : Type}
    (mu : q6813106_measure_space A)
    (P : A -> Prop) : Prop :=
  exists null_set : q6813106_set A,
    q6813106_measurable mu null_set /\
    q6813106_ennreal_eq
      (q6813106_measure mu null_set)
      q6813106_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q6813106_normed_real_vector_space (G : Type) : Type := {
  q6813106_zero : G;
  q6813106_add : G -> G -> G;
  q6813106_neg : G -> G;
  q6813106_smul : R -> G -> G;
  q6813106_norm : G -> R;
  q6813106_add_assoc :
    forall x y z : G,
      q6813106_add x (q6813106_add y z) =
      q6813106_add (q6813106_add x y) z;
  q6813106_add_comm :
    forall x y : G, q6813106_add x y = q6813106_add y x;
  q6813106_add_zero :
    forall x : G, q6813106_add x q6813106_zero = x;
  q6813106_add_neg :
    forall x : G,
      q6813106_add x (q6813106_neg x) = q6813106_zero;
  q6813106_one_smul :
    forall x : G, q6813106_smul 1 x = x;
  q6813106_mul_smul :
    forall (a b : R) (x : G),
      q6813106_smul (a * b) x =
      q6813106_smul a (q6813106_smul b x);
  q6813106_add_smul :
    forall (a b : R) (x : G),
      q6813106_smul (a + b) x =
      q6813106_add (q6813106_smul a x) (q6813106_smul b x);
  q6813106_smul_add :
    forall (a : R) (x y : G),
      q6813106_smul a (q6813106_add x y) =
      q6813106_add (q6813106_smul a x) (q6813106_smul a y);
  q6813106_zero_smul :
    forall x : G, q6813106_smul 0 x = q6813106_zero;
  q6813106_smul_zero :
    forall a : R, q6813106_smul a q6813106_zero = q6813106_zero;
  q6813106_norm_nonnegative :
    forall x : G, 0 <= q6813106_norm x;
  q6813106_norm_eq_zero :
    forall x : G,
      q6813106_norm x = 0 <-> x = q6813106_zero;
  q6813106_norm_add_le :
    forall x y : G,
      q6813106_norm (q6813106_add x y) <=
      q6813106_norm x + q6813106_norm y;
  q6813106_norm_smul :
    forall (a : R) (x : G),
      q6813106_norm (q6813106_smul a x) =
      Rabs a * q6813106_norm x
}.

Arguments q6813106_zero {G} _.
Arguments q6813106_add {G} _ _ _.
Arguments q6813106_neg {G} _ _.
Arguments q6813106_smul {G} _ _ _.
Arguments q6813106_norm {G} _ _.

Definition q6813106_sub {G : Type}
    (V : q6813106_normed_real_vector_space G)
    (x y : G) : G :=
  q6813106_add V x (q6813106_neg V y).

Record q6813106_complex : Type := {
  q6813106_re : R;
  q6813106_im : R
}.

Definition q6813106_czero : q6813106_complex :=
  {| q6813106_re := 0; q6813106_im := 0 |}.

Definition q6813106_cone : q6813106_complex :=
  {| q6813106_re := 1; q6813106_im := 0 |}.

Definition q6813106_ci : q6813106_complex :=
  {| q6813106_re := 0; q6813106_im := 1 |}.

Definition q6813106_cadd
    (z w : q6813106_complex) : q6813106_complex :=
  {| q6813106_re := q6813106_re z + q6813106_re w;
     q6813106_im := q6813106_im z + q6813106_im w |}.

Definition q6813106_cmul
    (z w : q6813106_complex) : q6813106_complex :=
  {| q6813106_re :=
       q6813106_re z * q6813106_re w -
       q6813106_im z * q6813106_im w;
     q6813106_im :=
       q6813106_re z * q6813106_im w +
       q6813106_im z * q6813106_re w |}.

Definition q6813106_cneg (z : q6813106_complex) : q6813106_complex :=
  {| q6813106_re := - q6813106_re z;
     q6813106_im := - q6813106_im z |}.

Definition q6813106_csub
    (z w : q6813106_complex) : q6813106_complex :=
  q6813106_cadd z (q6813106_cneg w).

Definition q6813106_real_to_complex (x : R) : q6813106_complex :=
  {| q6813106_re := x; q6813106_im := 0 |}.

Definition q6813106_complex_modulus (z : q6813106_complex) : R :=
  sqrt
    (q6813106_re z * q6813106_re z +
     q6813106_im z * q6813106_im z).

Definition q6813106_complex_exp (z : q6813106_complex) : q6813106_complex :=
  {| q6813106_re := exp (q6813106_re z) * cos (q6813106_im z);
     q6813106_im := exp (q6813106_re z) * sin (q6813106_im z) |}.

Record q6813106_complex_normed_space
    {E : Type}
    (V : q6813106_normed_real_vector_space E) : Type := {
  q6813106_csmul : q6813106_complex -> E -> E;
  q6813106_csmul_one :
    forall x : E, q6813106_csmul q6813106_cone x = x;
  q6813106_csmul_mul :
    forall (a b : q6813106_complex) (x : E),
      q6813106_csmul (q6813106_cmul a b) x =
      q6813106_csmul a (q6813106_csmul b x);
  q6813106_csmul_add_scalar :
    forall (a b : q6813106_complex) (x : E),
      q6813106_csmul (q6813106_cadd a b) x =
      q6813106_add V (q6813106_csmul a x) (q6813106_csmul b x);
  q6813106_csmul_add_vector :
    forall (a : q6813106_complex) (x y : E),
      q6813106_csmul a (q6813106_add V x y) =
      q6813106_add V (q6813106_csmul a x) (q6813106_csmul a y);
  q6813106_csmul_real :
    forall (a : R) (x : E),
      q6813106_csmul (q6813106_real_to_complex a) x =
      q6813106_smul V a x;
  q6813106_norm_csmul :
    forall (a : q6813106_complex) (x : E),
      q6813106_norm V (q6813106_csmul a x) =
      q6813106_complex_modulus a * q6813106_norm V x
}.

Arguments q6813106_csmul {E V} _ _ _.

Definition q6813106_real_open
    (U : q6813106_set R) : Prop :=
  forall x : R,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : R,
        Rabs (y - x) < radius ->
        U y.

Definition q6813106_real_borel_set
    (S : q6813106_set R) : Prop :=
  forall classes : q6813106_set (q6813106_set R),
    q6813106_sigma_class classes ->
    (forall U : q6813106_set R,
      q6813106_real_open U -> classes U) ->
    classes S.

Definition q6813106_unit_interval : q6813106_set R :=
  fun x => 0 < x <= 1.

Definition q6813106_is_real_lebesgue_measure
    (mu : q6813106_measure_space R) : Prop :=
  (forall S : q6813106_set R,
      q6813106_measurable mu S <-> q6813106_real_borel_set S) /\
  (forall (a : R) (S : q6813106_set R),
      q6813106_ennreal_eq
        (q6813106_measure mu
          (fun x => S (a + x)))
        (q6813106_measure mu S)) /\
  q6813106_ennreal_eq
    (q6813106_measure mu q6813106_unit_interval)
    (q6813106_ennreal_finite 1 Rle_0_1).

Definition q6813106_vector_sequence_converges {G : Type}
    (V : q6813106_normed_real_vector_space G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q6813106_norm V
          (q6813106_sub V (u n) limit) < epsilon.

Definition q6813106_vector_sequence_cauchy {G : Type}
    (V : q6813106_normed_real_vector_space G)
    (u : nat -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q6813106_norm V
          (q6813106_sub V (u m) (u n)) < epsilon.

Definition q6813106_complete {G : Type}
    (V : q6813106_normed_real_vector_space G) : Prop :=
  forall u : nat -> G,
    q6813106_vector_sequence_cauchy V u ->
    exists limit : G,
      q6813106_vector_sequence_converges V u limit.

Definition q6813106_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q6813106_finite_partition {A : Type}
    (mu : q6813106_measure_space A)
    (k : nat) (cells : nat -> q6813106_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q6813106_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q6813106_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q6813106_measurable_simple {A G : Type}
    (mu : q6813106_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q6813106_set A),
    q6813106_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q6813106_ae_strongly_measurable {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q6813106_measurable_simple mu (approximants n)) /\
    q6813106_almost_everywhere mu
      (fun x =>
        q6813106_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q6813106_nonnegative_real : Type := {
  q6813106_nnreal_value : R;
  q6813106_nnreal_nonnegative : 0 <= q6813106_nnreal_value
}.

Definition q6813106_ennreal_of_nonnegative
    (x : q6813106_nonnegative_real) : q6813106_ennreal :=
  q6813106_ennreal_finite
    (q6813106_nnreal_value x)
    (q6813106_nnreal_nonnegative x).

Definition q6813106_simple_lintegral_below {A : Type}
    (mu : q6813106_measure_space A)
    (f : A -> q6813106_ennreal)
    (value : q6813106_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q6813106_nonnegative_real)
         (cells : nat -> q6813106_set A),
    q6813106_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q6813106_ennreal_le
        (q6813106_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q6813106_ennreal_eq value
      (q6813106_ennreal_partial_sum
        (fun i =>
          q6813106_ennreal_mul
            (q6813106_ennreal_of_nonnegative (coefficients i))
            (q6813106_measure mu (cells i)))
        k).

Definition q6813106_lintegral_has_value {A : Type}
    (mu : q6813106_measure_space A)
    (f : A -> q6813106_ennreal)
    (value : q6813106_ennreal) : Prop :=
  q6813106_ennreal_supremum
    (q6813106_simple_lintegral_below mu f) value.

Definition q6813106_norm_ennreal {G : Type}
    (V : q6813106_normed_real_vector_space G)
    (x : G) : q6813106_ennreal :=
  q6813106_ennreal_finite
    (q6813106_norm V x)
    (q6813106_norm_nonnegative V x).

Definition q6813106_integrable {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (f : A -> G) : Prop :=
  q6813106_ae_strongly_measurable V mu f /\
  exists value : q6813106_ennreal,
    q6813106_lintegral_has_value mu
      (fun x => q6813106_norm_ennreal V (f x)) value /\
    q6813106_ennreal_finite_value value.

Fixpoint q6813106_vector_sum {G : Type}
    (V : q6813106_normed_real_vector_space G)
    (u : nat -> G) (n : nat) : G :=
  match n with
  | O => q6813106_zero V
  | S k =>
      q6813106_add V
        (q6813106_vector_sum V u k) (u k)
  end.

Definition q6813106_weighted_cell_value {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (cell : q6813106_set A)
    (coefficient value : G) : Prop :=
  (coefficient = q6813106_zero V /\
    value = q6813106_zero V) \/
  exists mass : R,
    q6813106_ennreal_represents
      (q6813106_measure mu cell) mass /\
    value = q6813106_smul V mass coefficient.

Definition q6813106_simple_integral_has_value {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (s : A -> G) (value : G) : Prop :=
  exists (k : nat) (coefficients terms : nat -> G)
         (cells : nat -> q6813106_set A),
    q6813106_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q6813106_weighted_cell_value
        V mu (cells i) (coefficients i) (terms i)) /\
    value = q6813106_vector_sum V terms k.

Definition q6813106_l1_approximates {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (approximants : nat -> A -> G)
    (f : A -> G) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q6813106_ennreal,
        q6813106_lintegral_has_value mu
          (fun x =>
            q6813106_norm_ennreal V
              (q6813106_sub V (approximants n x) (f x)))
          integral_error /\
        q6813106_ennreal_represents
          integral_error (errors n)) /\
    q6813106_real_sequence_converges errors 0.

Definition q6813106_standard_bochner_integral_value {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  exists (approximants : nat -> A -> G)
         (integrals : nat -> G),
    (forall n : nat,
      q6813106_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q6813106_simple_integral_has_value
        V mu (approximants n) (integrals n)) /\
    q6813106_l1_approximates V mu approximants f /\
    q6813106_vector_sequence_converges V integrals value.

Definition q6813106_bochner_integral {A G : Type}
    (V : q6813106_normed_real_vector_space G)
    (mu : q6813106_measure_space A)
    (f : A -> G) : G :=
  match excluded_middle_informative
          (exists value : G,
            q6813106_standard_bochner_integral_value V mu f value) with
  | left _ =>
      epsilon (inhabits (q6813106_zero V))
        (fun value : G =>
          q6813106_standard_bochner_integral_value V mu f value)
  | right _ => q6813106_zero V
  end.

Definition q6813106_continuous_at_real
    {E : Type}
    (NE : q6813106_normed_real_vector_space E)
    (f : R -> E) (x : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : R,
        Rabs (y - x) < delta ->
        q6813106_norm NE
          (q6813106_sub NE (f y) (f x)) < epsilon.

Definition q6813106_real_cpow
    (x : R) (s : q6813106_complex) : q6813106_complex :=
  q6813106_complex_exp
    (q6813106_cmul s (q6813106_real_to_complex (ln x))).

Definition q6813106_vertical_point
    (sigma y : R) : q6813106_complex :=
  q6813106_cadd
    (q6813106_real_to_complex sigma)
    (q6813106_cmul (q6813106_real_to_complex y) q6813106_ci).

Definition q6813106_mellin_integrand
    {E : Type}
    {NE : q6813106_normed_real_vector_space E}
    (CE : q6813106_complex_normed_space NE)
    (f : R -> E) (s : q6813106_complex) (t : R) : E :=
  if Rlt_dec 0 t then
    q6813106_csmul CE
      (q6813106_real_cpow t
        (q6813106_csub s q6813106_cone))
      (f t)
  else q6813106_zero NE.

Definition q6813106_mellin_convergent
    {E : Type}
    (NE : q6813106_normed_real_vector_space E)
    (CE : q6813106_complex_normed_space NE)
    (mu : q6813106_measure_space R)
    (f : R -> E) (s : q6813106_complex) : Prop :=
  q6813106_integrable NE mu
    (q6813106_mellin_integrand CE f s).

Definition q6813106_mellin
    {E : Type}
    (NE : q6813106_normed_real_vector_space E)
    (CE : q6813106_complex_normed_space NE)
    (mu : q6813106_measure_space R)
    (f : R -> E) (s : q6813106_complex) : E :=
  q6813106_bochner_integral NE mu
    (q6813106_mellin_integrand CE f s).

Definition q6813106_vertical_integrable
    {E : Type}
    (NE : q6813106_normed_real_vector_space E)
    (mu : q6813106_measure_space R)
    (F : q6813106_complex -> E) (sigma : R) : Prop :=
  q6813106_integrable NE mu
    (fun y => F (q6813106_vertical_point sigma y)).

Definition q6813106_mellin_inverse
    {E : Type}
    (NE : q6813106_normed_real_vector_space E)
    (CE : q6813106_complex_normed_space NE)
    (mu : q6813106_measure_space R)
    (sigma : R) (F : q6813106_complex -> E) (x : R) : E :=
  q6813106_smul NE (1 / (2 * PI))
    (q6813106_bochner_integral NE mu
      (fun y =>
        let s := q6813106_vertical_point sigma y in
        q6813106_csmul CE
          (q6813106_real_cpow x (q6813106_cneg s))
          (F s))).

Theorem mellin_inversion :
  forall (E : Type)
         (NE : q6813106_normed_real_vector_space E)
         (CE : q6813106_complex_normed_space NE)
         (mu : q6813106_measure_space R)
         (sigma : R) (f : R -> E) (x : R),
    q6813106_is_real_lebesgue_measure mu ->
    q6813106_complete NE ->
    0 < x ->
    @q6813106_mellin_convergent E NE CE mu f
      (q6813106_real_to_complex sigma) ->
    q6813106_vertical_integrable NE mu
      (@q6813106_mellin E NE CE mu f) sigma ->
    q6813106_continuous_at_real NE f x ->
    @q6813106_mellin_inverse E NE CE mu sigma
      (@q6813106_mellin E NE CE mu f) x = f x.
Admitted.
