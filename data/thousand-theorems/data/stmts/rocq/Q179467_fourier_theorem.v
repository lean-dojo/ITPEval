(*
  Statement-only formalization of Thousand Theorems corpus artifact Q179467
  (thousand-theorems__rocq__Q179467), "Fourier theorem": Fourier inversion
  for integrable functions on finite-dimensional real inner-product spaces,
  pointwise at continuity points and globally for continuous functions.
  This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals ClassicalDescription
  ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q179467_set (A : Type) : Type := A -> Prop.

Definition q179467_empty {A : Type} : q179467_set A :=
  fun _ => False.

Definition q179467_full {A : Type} : q179467_set A :=
  fun _ => True.

Definition q179467_complement {A : Type}
    (E : q179467_set A) : q179467_set A :=
  fun x => ~ E x.

Definition q179467_countable_union {A : Type}
    (E : nat -> q179467_set A) : q179467_set A :=
  fun x => exists n : nat, E n x.

Definition q179467_same_set {A : Type}
    (E F : q179467_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q179467_disjoint {A : Type}
    (E F : q179467_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q179467_pairwise_disjoint {A : Type}
    (E : nat -> q179467_set A) : Prop :=
  forall i j : nat, i <> j -> q179467_disjoint (E i) (E j).

Definition q179467_sigma_class {A : Type}
    (C : q179467_set (q179467_set A)) : Prop :=
  C q179467_empty /\
  (forall E F : q179467_set A,
    q179467_same_set E F ->
    C E ->
    C F) /\
  (forall E : q179467_set A,
    C E -> C (q179467_complement E)) /\
  (forall E : nat -> q179467_set A,
    (forall n : nat, C (E n)) ->
    C (q179467_countable_union E)).

Inductive q179467_ennreal : Type :=
| q179467_ennreal_finite :
    forall value : R, 0 <= value -> q179467_ennreal
| q179467_ennreal_infinity : q179467_ennreal.

Arguments q179467_ennreal_finite value nonnegative : clear implicits.

Definition q179467_ennreal_zero : q179467_ennreal :=
  q179467_ennreal_finite 0 (Rle_refl 0).

Definition q179467_ennreal_eq
    (x y : q179467_ennreal) : Prop :=
  match x, y with
  | q179467_ennreal_finite a _,
    q179467_ennreal_finite b _ => a = b
  | q179467_ennreal_infinity,
    q179467_ennreal_infinity => True
  | _, _ => False
  end.

Definition q179467_ennreal_le
    (x y : q179467_ennreal) : Prop :=
  match x, y with
  | q179467_ennreal_finite a _,
    q179467_ennreal_finite b _ => a <= b
  | q179467_ennreal_finite _ _,
    q179467_ennreal_infinity => True
  | q179467_ennreal_infinity,
    q179467_ennreal_finite _ _ => False
  | q179467_ennreal_infinity,
    q179467_ennreal_infinity => True
  end.

Definition q179467_ennreal_add
    (x y : q179467_ennreal) : q179467_ennreal :=
  match x, y with
  | q179467_ennreal_finite a ha,
    q179467_ennreal_finite b hb =>
      q179467_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q179467_ennreal_infinity
  end.

Definition q179467_ennreal_mul
    (x y : q179467_ennreal) : q179467_ennreal :=
  match x, y with
  | q179467_ennreal_finite a ha,
    q179467_ennreal_finite b hb =>
      q179467_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q179467_ennreal_finite a _, q179467_ennreal_infinity
  | q179467_ennreal_infinity, q179467_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q179467_ennreal_zero
      else q179467_ennreal_infinity
  | q179467_ennreal_infinity, q179467_ennreal_infinity =>
      q179467_ennreal_infinity
  end.

Fixpoint q179467_ennreal_partial_sum
    (u : nat -> q179467_ennreal)
    (n : nat) : q179467_ennreal :=
  match n with
  | O => q179467_ennreal_zero
  | S k =>
      q179467_ennreal_add
        (q179467_ennreal_partial_sum u k) (u k)
  end.

Definition q179467_ennreal_supremum
    (values : q179467_ennreal -> Prop)
    (bound : q179467_ennreal) : Prop :=
  (forall value : q179467_ennreal,
      values value -> q179467_ennreal_le value bound) /\
  (forall upper : q179467_ennreal,
      (forall value : q179467_ennreal,
        values value -> q179467_ennreal_le value upper) ->
      q179467_ennreal_le bound upper).

Definition q179467_ennreal_series_sum
    (u : nat -> q179467_ennreal)
    (sum : q179467_ennreal) : Prop :=
  q179467_ennreal_supremum
    (fun value =>
      exists n : nat,
        q179467_ennreal_eq value
          (q179467_ennreal_partial_sum u n))
    sum.

Definition q179467_ennreal_represents
    (x : q179467_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q179467_ennreal_eq x
      (q179467_ennreal_finite value nonnegative).

Definition q179467_ennreal_finite_value
    (x : q179467_ennreal) : Prop :=
  exists value : R, q179467_ennreal_represents x value.

Record q179467_measure_space (A : Type) : Type := {
  q179467_measurable : q179467_set A -> Prop;
  q179467_measurable_extensional :
    forall E F : q179467_set A,
      q179467_same_set E F ->
      (q179467_measurable E <-> q179467_measurable F);
  q179467_measurable_empty :
    q179467_measurable q179467_empty;
  q179467_measurable_complement :
    forall E : q179467_set A,
      q179467_measurable E ->
      q179467_measurable (q179467_complement E);
  q179467_measurable_countable_union :
    forall E : nat -> q179467_set A,
      (forall n : nat, q179467_measurable (E n)) ->
      q179467_measurable (q179467_countable_union E);
  q179467_measure : q179467_set A -> q179467_ennreal;
  q179467_measure_extensional :
    forall E F : q179467_set A,
      q179467_same_set E F ->
      q179467_ennreal_eq
        (q179467_measure E) (q179467_measure F);
  q179467_measure_empty :
    q179467_ennreal_eq
      (q179467_measure q179467_empty)
      q179467_ennreal_zero;
  q179467_measure_countable_additive :
    forall E : nat -> q179467_set A,
      (forall n : nat, q179467_measurable (E n)) ->
      q179467_pairwise_disjoint E ->
      q179467_ennreal_series_sum
        (fun n => q179467_measure (E n))
        (q179467_measure (q179467_countable_union E))
}.

Arguments q179467_measurable {A} _ _.
Arguments q179467_measure {A} _ _.

Definition q179467_almost_everywhere {A : Type}
    (mu : q179467_measure_space A)
    (P : A -> Prop) : Prop :=
  exists null_set : q179467_set A,
    q179467_measurable mu null_set /\
    q179467_ennreal_eq
      (q179467_measure mu null_set)
      q179467_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q179467_normed_real_vector_space (G : Type) : Type := {
  q179467_zero : G;
  q179467_add : G -> G -> G;
  q179467_neg : G -> G;
  q179467_smul : R -> G -> G;
  q179467_norm : G -> R;
  q179467_add_assoc :
    forall x y z : G,
      q179467_add x (q179467_add y z) =
      q179467_add (q179467_add x y) z;
  q179467_add_comm :
    forall x y : G, q179467_add x y = q179467_add y x;
  q179467_add_zero :
    forall x : G, q179467_add x q179467_zero = x;
  q179467_add_neg :
    forall x : G,
      q179467_add x (q179467_neg x) = q179467_zero;
  q179467_one_smul :
    forall x : G, q179467_smul 1 x = x;
  q179467_mul_smul :
    forall (a b : R) (x : G),
      q179467_smul (a * b) x =
      q179467_smul a (q179467_smul b x);
  q179467_add_smul :
    forall (a b : R) (x : G),
      q179467_smul (a + b) x =
      q179467_add (q179467_smul a x) (q179467_smul b x);
  q179467_smul_add :
    forall (a : R) (x y : G),
      q179467_smul a (q179467_add x y) =
      q179467_add (q179467_smul a x) (q179467_smul a y);
  q179467_zero_smul :
    forall x : G, q179467_smul 0 x = q179467_zero;
  q179467_smul_zero :
    forall a : R, q179467_smul a q179467_zero = q179467_zero;
  q179467_norm_nonnegative :
    forall x : G, 0 <= q179467_norm x;
  q179467_norm_eq_zero :
    forall x : G,
      q179467_norm x = 0 <-> x = q179467_zero;
  q179467_norm_add_le :
    forall x y : G,
      q179467_norm (q179467_add x y) <=
      q179467_norm x + q179467_norm y;
  q179467_norm_smul :
    forall (a : R) (x : G),
      q179467_norm (q179467_smul a x) =
      Rabs a * q179467_norm x
}.

Arguments q179467_zero {G} _.
Arguments q179467_add {G} _ _ _.
Arguments q179467_neg {G} _ _.
Arguments q179467_smul {G} _ _ _.
Arguments q179467_norm {G} _ _.

Definition q179467_sub {G : Type}
    (V : q179467_normed_real_vector_space G)
    (x y : G) : G :=
  q179467_add V x (q179467_neg V y).

Record q179467_complex : Type := {
  q179467_re : R;
  q179467_im : R
}.

Definition q179467_czero : q179467_complex :=
  {| q179467_re := 0; q179467_im := 0 |}.

Definition q179467_cone : q179467_complex :=
  {| q179467_re := 1; q179467_im := 0 |}.

Definition q179467_ci : q179467_complex :=
  {| q179467_re := 0; q179467_im := 1 |}.

Definition q179467_cadd
    (z w : q179467_complex) : q179467_complex :=
  {| q179467_re := q179467_re z + q179467_re w;
     q179467_im := q179467_im z + q179467_im w |}.

Definition q179467_cmul
    (z w : q179467_complex) : q179467_complex :=
  {| q179467_re :=
       q179467_re z * q179467_re w -
       q179467_im z * q179467_im w;
     q179467_im :=
       q179467_re z * q179467_im w +
       q179467_im z * q179467_re w |}.

Definition q179467_real_to_complex (x : R) : q179467_complex :=
  {| q179467_re := x; q179467_im := 0 |}.

Definition q179467_complex_modulus (z : q179467_complex) : R :=
  sqrt
    (q179467_re z * q179467_re z +
     q179467_im z * q179467_im z).

Definition q179467_complex_exp (z : q179467_complex) : q179467_complex :=
  {| q179467_re := exp (q179467_re z) * cos (q179467_im z);
     q179467_im := exp (q179467_re z) * sin (q179467_im z) |}.

Record q179467_complex_normed_space
    {E : Type}
    (V : q179467_normed_real_vector_space E) : Type := {
  q179467_csmul : q179467_complex -> E -> E;
  q179467_csmul_one :
    forall x : E, q179467_csmul q179467_cone x = x;
  q179467_csmul_mul :
    forall (a b : q179467_complex) (x : E),
      q179467_csmul (q179467_cmul a b) x =
      q179467_csmul a (q179467_csmul b x);
  q179467_csmul_add_scalar :
    forall (a b : q179467_complex) (x : E),
      q179467_csmul (q179467_cadd a b) x =
      q179467_add V (q179467_csmul a x) (q179467_csmul b x);
  q179467_csmul_add_vector :
    forall (a : q179467_complex) (x y : E),
      q179467_csmul a (q179467_add V x y) =
      q179467_add V (q179467_csmul a x) (q179467_csmul a y);
  q179467_csmul_real :
    forall (a : R) (x : E),
      q179467_csmul (q179467_real_to_complex a) x =
      q179467_smul V a x;
  q179467_norm_csmul :
    forall (a : q179467_complex) (x : E),
      q179467_norm V (q179467_csmul a x) =
      q179467_complex_modulus a * q179467_norm V x
}.

Arguments q179467_csmul {E V} _ _ _.

Record q179467_real_inner_product_space
    {V : Type}
    (N : q179467_normed_real_vector_space V) : Type := {
  q179467_inner : V -> V -> R;
  q179467_inner_add_left :
    forall x y z : V,
      q179467_inner (q179467_add N x y) z =
      q179467_inner x z + q179467_inner y z;
  q179467_inner_smul_left :
    forall (a : R) (x y : V),
      q179467_inner (q179467_smul N a x) y =
      a * q179467_inner x y;
  q179467_inner_symmetric :
    forall x y : V, q179467_inner x y = q179467_inner y x;
  q179467_inner_norm_sq :
    forall x : V,
      q179467_inner x x = q179467_norm N x * q179467_norm N x
}.

Arguments q179467_inner {V N} _ _ _.

Fixpoint q179467_coordinate_sum
    {V : Type}
    (N : q179467_normed_real_vector_space V)
    (n : nat) : (Fin.t n -> V) -> V :=
  match n as k return (Fin.t k -> V) -> V with
  | O => fun _ => q179467_zero N
  | S k =>
      fun terms =>
        q179467_add N
          (terms Fin.F1)
          (@q179467_coordinate_sum V N k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q179467_coordinate_sum {V} N n _.

Record q179467_finite_dimensional
    {V : Type}
    {N : q179467_normed_real_vector_space V}
    (H : q179467_real_inner_product_space N) : Type := {
  q179467_dimension : nat;
  q179467_basis : Fin.t q179467_dimension -> V;
  q179467_coordinates : V -> Fin.t q179467_dimension -> R;
  q179467_coordinate_reconstruction :
    forall x : V,
      x =
      q179467_coordinate_sum N q179467_dimension
        (fun i =>
          q179467_smul N
            (q179467_coordinates x i) (q179467_basis i));
  q179467_coordinates_add :
    forall (x y : V) (i : Fin.t q179467_dimension),
      q179467_coordinates (q179467_add N x y) i =
      q179467_coordinates x i + q179467_coordinates y i;
  q179467_coordinates_smul :
    forall (a : R) (x : V) (i : Fin.t q179467_dimension),
      q179467_coordinates (q179467_smul N a x) i =
      a * q179467_coordinates x i;
  q179467_basis_orthonormal :
    forall i j : Fin.t q179467_dimension,
      q179467_inner H (q179467_basis i) (q179467_basis j) =
      if Fin.eq_dec i j then 1 else 0
}.

Arguments q179467_dimension {V N H} _.
Arguments q179467_basis {V N H} _ _.
Arguments q179467_coordinates {V N H} _ _ _.

Definition q179467_open {V : Type}
    (N : q179467_normed_real_vector_space V)
    (U : q179467_set V) : Prop :=
  forall x : V,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : V,
        q179467_norm N (q179467_sub N y x) < radius ->
        U y.

Definition q179467_borel_set {V : Type}
    (N : q179467_normed_real_vector_space V)
    (S : q179467_set V) : Prop :=
  forall classes : q179467_set (q179467_set V),
    q179467_sigma_class classes ->
    (forall U : q179467_set V, q179467_open N U -> classes U) ->
    classes S.

Definition q179467_unit_coordinate_cube
    {V : Type}
    {N : q179467_normed_real_vector_space V}
    {H : q179467_real_inner_product_space N}
    (D : q179467_finite_dimensional H) : q179467_set V :=
  fun x =>
    forall i : Fin.t (q179467_dimension D),
      0 < q179467_coordinates D x i <= 1.

Definition q179467_is_euclidean_lebesgue_measure
    {V : Type}
    {N : q179467_normed_real_vector_space V}
    {H : q179467_real_inner_product_space N}
    (D : q179467_finite_dimensional H)
    (mu : q179467_measure_space V) : Prop :=
  (forall S : q179467_set V,
      q179467_measurable mu S <-> q179467_borel_set N S) /\
  (forall (a : V) (S : q179467_set V),
      q179467_ennreal_eq
        (q179467_measure mu
          (fun x => S (q179467_add N a x)))
        (q179467_measure mu S)) /\
  q179467_ennreal_eq
    (q179467_measure mu (q179467_unit_coordinate_cube D))
    (q179467_ennreal_finite 1 Rle_0_1).

Definition q179467_vector_sequence_converges {G : Type}
    (V : q179467_normed_real_vector_space G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q179467_norm V
          (q179467_sub V (u n) limit) < epsilon.

Definition q179467_vector_sequence_cauchy {G : Type}
    (V : q179467_normed_real_vector_space G)
    (u : nat -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q179467_norm V
          (q179467_sub V (u m) (u n)) < epsilon.

Definition q179467_complete {G : Type}
    (V : q179467_normed_real_vector_space G) : Prop :=
  forall u : nat -> G,
    q179467_vector_sequence_cauchy V u ->
    exists limit : G,
      q179467_vector_sequence_converges V u limit.

Definition q179467_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q179467_finite_partition {A : Type}
    (mu : q179467_measure_space A)
    (k : nat) (cells : nat -> q179467_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q179467_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q179467_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q179467_measurable_simple {A G : Type}
    (mu : q179467_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q179467_set A),
    q179467_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q179467_ae_strongly_measurable {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q179467_measurable_simple mu (approximants n)) /\
    q179467_almost_everywhere mu
      (fun x =>
        q179467_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q179467_nonnegative_real : Type := {
  q179467_nnreal_value : R;
  q179467_nnreal_nonnegative : 0 <= q179467_nnreal_value
}.

Definition q179467_ennreal_of_nonnegative
    (x : q179467_nonnegative_real) : q179467_ennreal :=
  q179467_ennreal_finite
    (q179467_nnreal_value x)
    (q179467_nnreal_nonnegative x).

Definition q179467_simple_lintegral_below {A : Type}
    (mu : q179467_measure_space A)
    (f : A -> q179467_ennreal)
    (value : q179467_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q179467_nonnegative_real)
         (cells : nat -> q179467_set A),
    q179467_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q179467_ennreal_le
        (q179467_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q179467_ennreal_eq value
      (q179467_ennreal_partial_sum
        (fun i =>
          q179467_ennreal_mul
            (q179467_ennreal_of_nonnegative (coefficients i))
            (q179467_measure mu (cells i)))
        k).

Definition q179467_lintegral_has_value {A : Type}
    (mu : q179467_measure_space A)
    (f : A -> q179467_ennreal)
    (value : q179467_ennreal) : Prop :=
  q179467_ennreal_supremum
    (q179467_simple_lintegral_below mu f) value.

Definition q179467_norm_ennreal {G : Type}
    (V : q179467_normed_real_vector_space G)
    (x : G) : q179467_ennreal :=
  q179467_ennreal_finite
    (q179467_norm V x)
    (q179467_norm_nonnegative V x).

Definition q179467_integrable {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (f : A -> G) : Prop :=
  q179467_ae_strongly_measurable V mu f /\
  exists value : q179467_ennreal,
    q179467_lintegral_has_value mu
      (fun x => q179467_norm_ennreal V (f x)) value /\
    q179467_ennreal_finite_value value.

Fixpoint q179467_vector_sum {G : Type}
    (V : q179467_normed_real_vector_space G)
    (u : nat -> G) (n : nat) : G :=
  match n with
  | O => q179467_zero V
  | S k =>
      q179467_add V
        (q179467_vector_sum V u k) (u k)
  end.

Definition q179467_weighted_cell_value {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (cell : q179467_set A)
    (coefficient value : G) : Prop :=
  (coefficient = q179467_zero V /\
    value = q179467_zero V) \/
  exists mass : R,
    q179467_ennreal_represents
      (q179467_measure mu cell) mass /\
    value = q179467_smul V mass coefficient.

Definition q179467_simple_integral_has_value {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (s : A -> G) (value : G) : Prop :=
  exists (k : nat) (coefficients terms : nat -> G)
         (cells : nat -> q179467_set A),
    q179467_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q179467_weighted_cell_value
        V mu (cells i) (coefficients i) (terms i)) /\
    value = q179467_vector_sum V terms k.

Definition q179467_l1_approximates {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (approximants : nat -> A -> G)
    (f : A -> G) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q179467_ennreal,
        q179467_lintegral_has_value mu
          (fun x =>
            q179467_norm_ennreal V
              (q179467_sub V (approximants n x) (f x)))
          integral_error /\
        q179467_ennreal_represents
          integral_error (errors n)) /\
    q179467_real_sequence_converges errors 0.

Definition q179467_standard_bochner_integral_value {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  exists (approximants : nat -> A -> G)
         (integrals : nat -> G),
    (forall n : nat,
      q179467_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q179467_simple_integral_has_value
        V mu (approximants n) (integrals n)) /\
    q179467_l1_approximates V mu approximants f /\
    q179467_vector_sequence_converges V integrals value.

Definition q179467_bochner_integral {A G : Type}
    (V : q179467_normed_real_vector_space G)
    (mu : q179467_measure_space A)
    (f : A -> G) : G :=
  match excluded_middle_informative
          (exists value : G,
            q179467_standard_bochner_integral_value V mu f value) with
  | left _ =>
      epsilon (inhabits (q179467_zero V))
        (fun value : G =>
          q179467_standard_bochner_integral_value V mu f value)
  | right _ => q179467_zero V
  end.

Definition q179467_continuous_at
    {V E : Type}
    (NV : q179467_normed_real_vector_space V)
    (NE : q179467_normed_real_vector_space E)
    (f : V -> E) (v : V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : V,
        q179467_norm NV (q179467_sub NV w v) < delta ->
        q179467_norm NE
          (q179467_sub NE (f w) (f v)) < epsilon.

Definition q179467_continuous
    {V E : Type}
    (NV : q179467_normed_real_vector_space V)
    (NE : q179467_normed_real_vector_space E)
    (f : V -> E) : Prop :=
  forall v : V, q179467_continuous_at NV NE f v.

Definition q179467_fourier_character (t : R) : q179467_complex :=
  q179467_complex_exp
    (q179467_cmul
      (q179467_real_to_complex (- (2 * PI * t)))
      q179467_ci).

Definition q179467_inverse_fourier_character
    (t : R) : q179467_complex :=
  q179467_complex_exp
    (q179467_cmul
      (q179467_real_to_complex (2 * PI * t))
      q179467_ci).

Definition q179467_fourier_transform
    {V E : Type}
    {NV : q179467_normed_real_vector_space V}
    (H : q179467_real_inner_product_space NV)
    {NE : q179467_normed_real_vector_space E}
    (CE : q179467_complex_normed_space NE)
    (mu : q179467_measure_space V)
    (f : V -> E) : V -> E :=
  fun w =>
    q179467_bochner_integral NE mu
      (fun x =>
        q179467_csmul CE
          (q179467_fourier_character
            (q179467_inner H x w))
          (f x)).

Definition q179467_inverse_fourier_transform
    {V E : Type}
    {NV : q179467_normed_real_vector_space V}
    (H : q179467_real_inner_product_space NV)
    {NE : q179467_normed_real_vector_space E}
    (CE : q179467_complex_normed_space NE)
    (mu : q179467_measure_space V)
    (f : V -> E) : V -> E :=
  fun v =>
    q179467_bochner_integral NE mu
      (fun w =>
        q179467_csmul CE
          (q179467_inverse_fourier_character
            (q179467_inner H w v))
          (f w)).

Theorem MeasureTheory_Integrable_fourier_inversion :
  forall (V E : Type)
         (NV : q179467_normed_real_vector_space V)
         (H : q179467_real_inner_product_space NV)
         (D : q179467_finite_dimensional H)
         (NE : q179467_normed_real_vector_space E)
         (CE : q179467_complex_normed_space NE)
         (mu : q179467_measure_space V)
         (f : V -> E) (v : V),
    q179467_is_euclidean_lebesgue_measure D mu ->
    q179467_complete NE ->
    q179467_integrable NE mu f ->
    q179467_integrable NE mu
      (q179467_fourier_transform H CE mu f) ->
    q179467_continuous_at NV NE f v ->
    q179467_inverse_fourier_transform H CE mu
      (q179467_fourier_transform H CE mu f) v = f v.
Admitted.

Theorem Continuous_fourier_inversion :
  forall (V E : Type)
         (NV : q179467_normed_real_vector_space V)
         (H : q179467_real_inner_product_space NV)
         (D : q179467_finite_dimensional H)
         (NE : q179467_normed_real_vector_space E)
         (CE : q179467_complex_normed_space NE)
         (mu : q179467_measure_space V)
         (f : V -> E),
    q179467_is_euclidean_lebesgue_measure D mu ->
    q179467_complete NE ->
    q179467_continuous NV NE f ->
    q179467_integrable NE mu f ->
    q179467_integrable NE mu
      (q179467_fourier_transform H CE mu f) ->
    forall v : V,
      q179467_inverse_fourier_transform H CE mu
        (q179467_fourier_transform H CE mu f) v = f v.
Admitted.
