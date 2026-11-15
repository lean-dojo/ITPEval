(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3984053
  (thousand-theorems__rocq__Q3984053), "Fourier inversion theorem": a
  continuous integrable function on a finite-dimensional real inner-product
  space is recovered pointwise by inverse Fourier transformation when its
  Fourier transform is integrable.
  This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals ClassicalDescription
  ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q3984053_set (A : Type) : Type := A -> Prop.

Definition q3984053_empty {A : Type} : q3984053_set A :=
  fun _ => False.

Definition q3984053_full {A : Type} : q3984053_set A :=
  fun _ => True.

Definition q3984053_complement {A : Type}
    (E : q3984053_set A) : q3984053_set A :=
  fun x => ~ E x.

Definition q3984053_countable_union {A : Type}
    (E : nat -> q3984053_set A) : q3984053_set A :=
  fun x => exists n : nat, E n x.

Definition q3984053_same_set {A : Type}
    (E F : q3984053_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q3984053_disjoint {A : Type}
    (E F : q3984053_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q3984053_pairwise_disjoint {A : Type}
    (E : nat -> q3984053_set A) : Prop :=
  forall i j : nat, i <> j -> q3984053_disjoint (E i) (E j).

Definition q3984053_sigma_class {A : Type}
    (C : q3984053_set (q3984053_set A)) : Prop :=
  C q3984053_empty /\
  (forall E F : q3984053_set A,
    q3984053_same_set E F ->
    C E ->
    C F) /\
  (forall E : q3984053_set A,
    C E -> C (q3984053_complement E)) /\
  (forall E : nat -> q3984053_set A,
    (forall n : nat, C (E n)) ->
    C (q3984053_countable_union E)).

Inductive q3984053_ennreal : Type :=
| q3984053_ennreal_finite :
    forall value : R, 0 <= value -> q3984053_ennreal
| q3984053_ennreal_infinity : q3984053_ennreal.

Arguments q3984053_ennreal_finite value nonnegative : clear implicits.

Definition q3984053_ennreal_zero : q3984053_ennreal :=
  q3984053_ennreal_finite 0 (Rle_refl 0).

Definition q3984053_ennreal_eq
    (x y : q3984053_ennreal) : Prop :=
  match x, y with
  | q3984053_ennreal_finite a _,
    q3984053_ennreal_finite b _ => a = b
  | q3984053_ennreal_infinity,
    q3984053_ennreal_infinity => True
  | _, _ => False
  end.

Definition q3984053_ennreal_le
    (x y : q3984053_ennreal) : Prop :=
  match x, y with
  | q3984053_ennreal_finite a _,
    q3984053_ennreal_finite b _ => a <= b
  | q3984053_ennreal_finite _ _,
    q3984053_ennreal_infinity => True
  | q3984053_ennreal_infinity,
    q3984053_ennreal_finite _ _ => False
  | q3984053_ennreal_infinity,
    q3984053_ennreal_infinity => True
  end.

Definition q3984053_ennreal_add
    (x y : q3984053_ennreal) : q3984053_ennreal :=
  match x, y with
  | q3984053_ennreal_finite a ha,
    q3984053_ennreal_finite b hb =>
      q3984053_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q3984053_ennreal_infinity
  end.

Definition q3984053_ennreal_mul
    (x y : q3984053_ennreal) : q3984053_ennreal :=
  match x, y with
  | q3984053_ennreal_finite a ha,
    q3984053_ennreal_finite b hb =>
      q3984053_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q3984053_ennreal_finite a _, q3984053_ennreal_infinity
  | q3984053_ennreal_infinity, q3984053_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q3984053_ennreal_zero
      else q3984053_ennreal_infinity
  | q3984053_ennreal_infinity, q3984053_ennreal_infinity =>
      q3984053_ennreal_infinity
  end.

Fixpoint q3984053_ennreal_partial_sum
    (u : nat -> q3984053_ennreal)
    (n : nat) : q3984053_ennreal :=
  match n with
  | O => q3984053_ennreal_zero
  | S k =>
      q3984053_ennreal_add
        (q3984053_ennreal_partial_sum u k) (u k)
  end.

Definition q3984053_ennreal_supremum
    (values : q3984053_ennreal -> Prop)
    (bound : q3984053_ennreal) : Prop :=
  (forall value : q3984053_ennreal,
      values value -> q3984053_ennreal_le value bound) /\
  (forall upper : q3984053_ennreal,
      (forall value : q3984053_ennreal,
        values value -> q3984053_ennreal_le value upper) ->
      q3984053_ennreal_le bound upper).

Definition q3984053_ennreal_series_sum
    (u : nat -> q3984053_ennreal)
    (sum : q3984053_ennreal) : Prop :=
  q3984053_ennreal_supremum
    (fun value =>
      exists n : nat,
        q3984053_ennreal_eq value
          (q3984053_ennreal_partial_sum u n))
    sum.

Definition q3984053_ennreal_represents
    (x : q3984053_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q3984053_ennreal_eq x
      (q3984053_ennreal_finite value nonnegative).

Definition q3984053_ennreal_finite_value
    (x : q3984053_ennreal) : Prop :=
  exists value : R, q3984053_ennreal_represents x value.

Record q3984053_measure_space (A : Type) : Type := {
  q3984053_measurable : q3984053_set A -> Prop;
  q3984053_measurable_extensional :
    forall E F : q3984053_set A,
      q3984053_same_set E F ->
      (q3984053_measurable E <-> q3984053_measurable F);
  q3984053_measurable_empty :
    q3984053_measurable q3984053_empty;
  q3984053_measurable_complement :
    forall E : q3984053_set A,
      q3984053_measurable E ->
      q3984053_measurable (q3984053_complement E);
  q3984053_measurable_countable_union :
    forall E : nat -> q3984053_set A,
      (forall n : nat, q3984053_measurable (E n)) ->
      q3984053_measurable (q3984053_countable_union E);
  q3984053_measure : q3984053_set A -> q3984053_ennreal;
  q3984053_measure_extensional :
    forall E F : q3984053_set A,
      q3984053_same_set E F ->
      q3984053_ennreal_eq
        (q3984053_measure E) (q3984053_measure F);
  q3984053_measure_empty :
    q3984053_ennreal_eq
      (q3984053_measure q3984053_empty)
      q3984053_ennreal_zero;
  q3984053_measure_countable_additive :
    forall E : nat -> q3984053_set A,
      (forall n : nat, q3984053_measurable (E n)) ->
      q3984053_pairwise_disjoint E ->
      q3984053_ennreal_series_sum
        (fun n => q3984053_measure (E n))
        (q3984053_measure (q3984053_countable_union E))
}.

Arguments q3984053_measurable {A} _ _.
Arguments q3984053_measure {A} _ _.

Definition q3984053_almost_everywhere {A : Type}
    (mu : q3984053_measure_space A)
    (P : A -> Prop) : Prop :=
  exists null_set : q3984053_set A,
    q3984053_measurable mu null_set /\
    q3984053_ennreal_eq
      (q3984053_measure mu null_set)
      q3984053_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q3984053_normed_real_vector_space (G : Type) : Type := {
  q3984053_zero : G;
  q3984053_add : G -> G -> G;
  q3984053_neg : G -> G;
  q3984053_smul : R -> G -> G;
  q3984053_norm : G -> R;
  q3984053_add_assoc :
    forall x y z : G,
      q3984053_add x (q3984053_add y z) =
      q3984053_add (q3984053_add x y) z;
  q3984053_add_comm :
    forall x y : G, q3984053_add x y = q3984053_add y x;
  q3984053_add_zero :
    forall x : G, q3984053_add x q3984053_zero = x;
  q3984053_add_neg :
    forall x : G,
      q3984053_add x (q3984053_neg x) = q3984053_zero;
  q3984053_one_smul :
    forall x : G, q3984053_smul 1 x = x;
  q3984053_mul_smul :
    forall (a b : R) (x : G),
      q3984053_smul (a * b) x =
      q3984053_smul a (q3984053_smul b x);
  q3984053_add_smul :
    forall (a b : R) (x : G),
      q3984053_smul (a + b) x =
      q3984053_add (q3984053_smul a x) (q3984053_smul b x);
  q3984053_smul_add :
    forall (a : R) (x y : G),
      q3984053_smul a (q3984053_add x y) =
      q3984053_add (q3984053_smul a x) (q3984053_smul a y);
  q3984053_zero_smul :
    forall x : G, q3984053_smul 0 x = q3984053_zero;
  q3984053_smul_zero :
    forall a : R, q3984053_smul a q3984053_zero = q3984053_zero;
  q3984053_norm_nonnegative :
    forall x : G, 0 <= q3984053_norm x;
  q3984053_norm_eq_zero :
    forall x : G,
      q3984053_norm x = 0 <-> x = q3984053_zero;
  q3984053_norm_add_le :
    forall x y : G,
      q3984053_norm (q3984053_add x y) <=
      q3984053_norm x + q3984053_norm y;
  q3984053_norm_smul :
    forall (a : R) (x : G),
      q3984053_norm (q3984053_smul a x) =
      Rabs a * q3984053_norm x
}.

Arguments q3984053_zero {G} _.
Arguments q3984053_add {G} _ _ _.
Arguments q3984053_neg {G} _ _.
Arguments q3984053_smul {G} _ _ _.
Arguments q3984053_norm {G} _ _.

Definition q3984053_sub {G : Type}
    (V : q3984053_normed_real_vector_space G)
    (x y : G) : G :=
  q3984053_add V x (q3984053_neg V y).

Record q3984053_complex : Type := {
  q3984053_re : R;
  q3984053_im : R
}.

Definition q3984053_czero : q3984053_complex :=
  {| q3984053_re := 0; q3984053_im := 0 |}.

Definition q3984053_cone : q3984053_complex :=
  {| q3984053_re := 1; q3984053_im := 0 |}.

Definition q3984053_ci : q3984053_complex :=
  {| q3984053_re := 0; q3984053_im := 1 |}.

Definition q3984053_cadd
    (z w : q3984053_complex) : q3984053_complex :=
  {| q3984053_re := q3984053_re z + q3984053_re w;
     q3984053_im := q3984053_im z + q3984053_im w |}.

Definition q3984053_cmul
    (z w : q3984053_complex) : q3984053_complex :=
  {| q3984053_re :=
       q3984053_re z * q3984053_re w -
       q3984053_im z * q3984053_im w;
     q3984053_im :=
       q3984053_re z * q3984053_im w +
       q3984053_im z * q3984053_re w |}.

Definition q3984053_real_to_complex (x : R) : q3984053_complex :=
  {| q3984053_re := x; q3984053_im := 0 |}.

Definition q3984053_complex_modulus (z : q3984053_complex) : R :=
  sqrt
    (q3984053_re z * q3984053_re z +
     q3984053_im z * q3984053_im z).

Definition q3984053_complex_exp (z : q3984053_complex) : q3984053_complex :=
  {| q3984053_re := exp (q3984053_re z) * cos (q3984053_im z);
     q3984053_im := exp (q3984053_re z) * sin (q3984053_im z) |}.

Record q3984053_complex_normed_space
    {E : Type}
    (V : q3984053_normed_real_vector_space E) : Type := {
  q3984053_csmul : q3984053_complex -> E -> E;
  q3984053_csmul_one :
    forall x : E, q3984053_csmul q3984053_cone x = x;
  q3984053_csmul_mul :
    forall (a b : q3984053_complex) (x : E),
      q3984053_csmul (q3984053_cmul a b) x =
      q3984053_csmul a (q3984053_csmul b x);
  q3984053_csmul_add_scalar :
    forall (a b : q3984053_complex) (x : E),
      q3984053_csmul (q3984053_cadd a b) x =
      q3984053_add V (q3984053_csmul a x) (q3984053_csmul b x);
  q3984053_csmul_add_vector :
    forall (a : q3984053_complex) (x y : E),
      q3984053_csmul a (q3984053_add V x y) =
      q3984053_add V (q3984053_csmul a x) (q3984053_csmul a y);
  q3984053_csmul_real :
    forall (a : R) (x : E),
      q3984053_csmul (q3984053_real_to_complex a) x =
      q3984053_smul V a x;
  q3984053_norm_csmul :
    forall (a : q3984053_complex) (x : E),
      q3984053_norm V (q3984053_csmul a x) =
      q3984053_complex_modulus a * q3984053_norm V x
}.

Arguments q3984053_csmul {E V} _ _ _.

Record q3984053_real_inner_product_space
    {V : Type}
    (N : q3984053_normed_real_vector_space V) : Type := {
  q3984053_inner : V -> V -> R;
  q3984053_inner_add_left :
    forall x y z : V,
      q3984053_inner (q3984053_add N x y) z =
      q3984053_inner x z + q3984053_inner y z;
  q3984053_inner_smul_left :
    forall (a : R) (x y : V),
      q3984053_inner (q3984053_smul N a x) y =
      a * q3984053_inner x y;
  q3984053_inner_symmetric :
    forall x y : V, q3984053_inner x y = q3984053_inner y x;
  q3984053_inner_norm_sq :
    forall x : V,
      q3984053_inner x x = q3984053_norm N x * q3984053_norm N x
}.

Arguments q3984053_inner {V N} _ _ _.

Fixpoint q3984053_coordinate_sum
    {V : Type}
    (N : q3984053_normed_real_vector_space V)
    (n : nat) : (Fin.t n -> V) -> V :=
  match n as k return (Fin.t k -> V) -> V with
  | O => fun _ => q3984053_zero N
  | S k =>
      fun terms =>
        q3984053_add N
          (terms Fin.F1)
          (@q3984053_coordinate_sum V N k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q3984053_coordinate_sum {V} N n _.

Record q3984053_finite_dimensional
    {V : Type}
    {N : q3984053_normed_real_vector_space V}
    (H : q3984053_real_inner_product_space N) : Type := {
  q3984053_dimension : nat;
  q3984053_basis : Fin.t q3984053_dimension -> V;
  q3984053_coordinates : V -> Fin.t q3984053_dimension -> R;
  q3984053_coordinate_reconstruction :
    forall x : V,
      x =
      q3984053_coordinate_sum N q3984053_dimension
        (fun i =>
          q3984053_smul N
            (q3984053_coordinates x i) (q3984053_basis i));
  q3984053_coordinates_add :
    forall (x y : V) (i : Fin.t q3984053_dimension),
      q3984053_coordinates (q3984053_add N x y) i =
      q3984053_coordinates x i + q3984053_coordinates y i;
  q3984053_coordinates_smul :
    forall (a : R) (x : V) (i : Fin.t q3984053_dimension),
      q3984053_coordinates (q3984053_smul N a x) i =
      a * q3984053_coordinates x i;
  q3984053_basis_orthonormal :
    forall i j : Fin.t q3984053_dimension,
      q3984053_inner H (q3984053_basis i) (q3984053_basis j) =
      if Fin.eq_dec i j then 1 else 0
}.

Arguments q3984053_dimension {V N H} _.
Arguments q3984053_basis {V N H} _ _.
Arguments q3984053_coordinates {V N H} _ _ _.

Definition q3984053_open {V : Type}
    (N : q3984053_normed_real_vector_space V)
    (U : q3984053_set V) : Prop :=
  forall x : V,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : V,
        q3984053_norm N (q3984053_sub N y x) < radius ->
        U y.

Definition q3984053_borel_set {V : Type}
    (N : q3984053_normed_real_vector_space V)
    (S : q3984053_set V) : Prop :=
  forall classes : q3984053_set (q3984053_set V),
    q3984053_sigma_class classes ->
    (forall U : q3984053_set V, q3984053_open N U -> classes U) ->
    classes S.

Definition q3984053_unit_coordinate_cube
    {V : Type}
    {N : q3984053_normed_real_vector_space V}
    {H : q3984053_real_inner_product_space N}
    (D : q3984053_finite_dimensional H) : q3984053_set V :=
  fun x =>
    forall i : Fin.t (q3984053_dimension D),
      0 < q3984053_coordinates D x i <= 1.

Definition q3984053_is_euclidean_lebesgue_measure
    {V : Type}
    {N : q3984053_normed_real_vector_space V}
    {H : q3984053_real_inner_product_space N}
    (D : q3984053_finite_dimensional H)
    (mu : q3984053_measure_space V) : Prop :=
  (forall S : q3984053_set V,
      q3984053_measurable mu S <-> q3984053_borel_set N S) /\
  (forall (a : V) (S : q3984053_set V),
      q3984053_ennreal_eq
        (q3984053_measure mu
          (fun x => S (q3984053_add N a x)))
        (q3984053_measure mu S)) /\
  q3984053_ennreal_eq
    (q3984053_measure mu (q3984053_unit_coordinate_cube D))
    (q3984053_ennreal_finite 1 Rle_0_1).

Definition q3984053_vector_sequence_converges {G : Type}
    (V : q3984053_normed_real_vector_space G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q3984053_norm V
          (q3984053_sub V (u n) limit) < epsilon.

Definition q3984053_vector_sequence_cauchy {G : Type}
    (V : q3984053_normed_real_vector_space G)
    (u : nat -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q3984053_norm V
          (q3984053_sub V (u m) (u n)) < epsilon.

Definition q3984053_complete {G : Type}
    (V : q3984053_normed_real_vector_space G) : Prop :=
  forall u : nat -> G,
    q3984053_vector_sequence_cauchy V u ->
    exists limit : G,
      q3984053_vector_sequence_converges V u limit.

Definition q3984053_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q3984053_finite_partition {A : Type}
    (mu : q3984053_measure_space A)
    (k : nat) (cells : nat -> q3984053_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q3984053_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q3984053_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q3984053_measurable_simple {A G : Type}
    (mu : q3984053_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q3984053_set A),
    q3984053_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q3984053_ae_strongly_measurable {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q3984053_measurable_simple mu (approximants n)) /\
    q3984053_almost_everywhere mu
      (fun x =>
        q3984053_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q3984053_nonnegative_real : Type := {
  q3984053_nnreal_value : R;
  q3984053_nnreal_nonnegative : 0 <= q3984053_nnreal_value
}.

Definition q3984053_ennreal_of_nonnegative
    (x : q3984053_nonnegative_real) : q3984053_ennreal :=
  q3984053_ennreal_finite
    (q3984053_nnreal_value x)
    (q3984053_nnreal_nonnegative x).

Definition q3984053_simple_lintegral_below {A : Type}
    (mu : q3984053_measure_space A)
    (f : A -> q3984053_ennreal)
    (value : q3984053_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q3984053_nonnegative_real)
         (cells : nat -> q3984053_set A),
    q3984053_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q3984053_ennreal_le
        (q3984053_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q3984053_ennreal_eq value
      (q3984053_ennreal_partial_sum
        (fun i =>
          q3984053_ennreal_mul
            (q3984053_ennreal_of_nonnegative (coefficients i))
            (q3984053_measure mu (cells i)))
        k).

Definition q3984053_lintegral_has_value {A : Type}
    (mu : q3984053_measure_space A)
    (f : A -> q3984053_ennreal)
    (value : q3984053_ennreal) : Prop :=
  q3984053_ennreal_supremum
    (q3984053_simple_lintegral_below mu f) value.

Definition q3984053_norm_ennreal {G : Type}
    (V : q3984053_normed_real_vector_space G)
    (x : G) : q3984053_ennreal :=
  q3984053_ennreal_finite
    (q3984053_norm V x)
    (q3984053_norm_nonnegative V x).

Definition q3984053_integrable {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (f : A -> G) : Prop :=
  q3984053_ae_strongly_measurable V mu f /\
  exists value : q3984053_ennreal,
    q3984053_lintegral_has_value mu
      (fun x => q3984053_norm_ennreal V (f x)) value /\
    q3984053_ennreal_finite_value value.

Fixpoint q3984053_vector_sum {G : Type}
    (V : q3984053_normed_real_vector_space G)
    (u : nat -> G) (n : nat) : G :=
  match n with
  | O => q3984053_zero V
  | S k =>
      q3984053_add V
        (q3984053_vector_sum V u k) (u k)
  end.

Definition q3984053_weighted_cell_value {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (cell : q3984053_set A)
    (coefficient value : G) : Prop :=
  (coefficient = q3984053_zero V /\
    value = q3984053_zero V) \/
  exists mass : R,
    q3984053_ennreal_represents
      (q3984053_measure mu cell) mass /\
    value = q3984053_smul V mass coefficient.

Definition q3984053_simple_integral_has_value {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (s : A -> G) (value : G) : Prop :=
  exists (k : nat) (coefficients terms : nat -> G)
         (cells : nat -> q3984053_set A),
    q3984053_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q3984053_weighted_cell_value
        V mu (cells i) (coefficients i) (terms i)) /\
    value = q3984053_vector_sum V terms k.

Definition q3984053_l1_approximates {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (approximants : nat -> A -> G)
    (f : A -> G) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q3984053_ennreal,
        q3984053_lintegral_has_value mu
          (fun x =>
            q3984053_norm_ennreal V
              (q3984053_sub V (approximants n x) (f x)))
          integral_error /\
        q3984053_ennreal_represents
          integral_error (errors n)) /\
    q3984053_real_sequence_converges errors 0.

Definition q3984053_standard_bochner_integral_value {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  exists (approximants : nat -> A -> G)
         (integrals : nat -> G),
    (forall n : nat,
      q3984053_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q3984053_simple_integral_has_value
        V mu (approximants n) (integrals n)) /\
    q3984053_l1_approximates V mu approximants f /\
    q3984053_vector_sequence_converges V integrals value.

Definition q3984053_bochner_integral {A G : Type}
    (V : q3984053_normed_real_vector_space G)
    (mu : q3984053_measure_space A)
    (f : A -> G) : G :=
  match excluded_middle_informative
          (exists value : G,
            q3984053_standard_bochner_integral_value V mu f value) with
  | left _ =>
      epsilon (inhabits (q3984053_zero V))
        (fun value : G =>
          q3984053_standard_bochner_integral_value V mu f value)
  | right _ => q3984053_zero V
  end.

Definition q3984053_continuous_at
    {V E : Type}
    (NV : q3984053_normed_real_vector_space V)
    (NE : q3984053_normed_real_vector_space E)
    (f : V -> E) (v : V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : V,
        q3984053_norm NV (q3984053_sub NV w v) < delta ->
        q3984053_norm NE
          (q3984053_sub NE (f w) (f v)) < epsilon.

Definition q3984053_continuous
    {V E : Type}
    (NV : q3984053_normed_real_vector_space V)
    (NE : q3984053_normed_real_vector_space E)
    (f : V -> E) : Prop :=
  forall v : V, q3984053_continuous_at NV NE f v.

Definition q3984053_fourier_character (t : R) : q3984053_complex :=
  q3984053_complex_exp
    (q3984053_cmul
      (q3984053_real_to_complex (- (2 * PI * t)))
      q3984053_ci).

Definition q3984053_inverse_fourier_character
    (t : R) : q3984053_complex :=
  q3984053_complex_exp
    (q3984053_cmul
      (q3984053_real_to_complex (2 * PI * t))
      q3984053_ci).

Definition q3984053_fourier_transform
    {V E : Type}
    {NV : q3984053_normed_real_vector_space V}
    (H : q3984053_real_inner_product_space NV)
    {NE : q3984053_normed_real_vector_space E}
    (CE : q3984053_complex_normed_space NE)
    (mu : q3984053_measure_space V)
    (f : V -> E) : V -> E :=
  fun w =>
    q3984053_bochner_integral NE mu
      (fun x =>
        q3984053_csmul CE
          (q3984053_fourier_character
            (q3984053_inner H x w))
          (f x)).

Definition q3984053_inverse_fourier_transform
    {V E : Type}
    {NV : q3984053_normed_real_vector_space V}
    (H : q3984053_real_inner_product_space NV)
    {NE : q3984053_normed_real_vector_space E}
    (CE : q3984053_complex_normed_space NE)
    (mu : q3984053_measure_space V)
    (f : V -> E) : V -> E :=
  fun v =>
    q3984053_bochner_integral NE mu
      (fun w =>
        q3984053_csmul CE
          (q3984053_inverse_fourier_character
            (q3984053_inner H w v))
          (f w)).

Theorem Continuous_fourier_inversion :
  forall (V E : Type)
         (NV : q3984053_normed_real_vector_space V)
         (H : q3984053_real_inner_product_space NV)
         (D : q3984053_finite_dimensional H)
         (NE : q3984053_normed_real_vector_space E)
         (CE : q3984053_complex_normed_space NE)
         (mu : q3984053_measure_space V)
         (f : V -> E),
    q3984053_is_euclidean_lebesgue_measure D mu ->
    q3984053_complete NE ->
    q3984053_continuous NV NE f ->
    q3984053_integrable NE mu f ->
    q3984053_integrable NE mu
      (q3984053_fourier_transform H CE mu f) ->
    forall v : V,
      q3984053_inverse_fourier_transform H CE mu
        (q3984053_fourier_transform H CE mu f) v = f v.
Admitted.
