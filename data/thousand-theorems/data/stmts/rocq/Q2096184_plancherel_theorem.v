(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2096184
  (thousand-theorems__rocq__Q2096184), "Plancherel theorem": the Fourier
  transform preserves the integral complex inner product of Hilbert-valued
  Schwartz functions on a finite-dimensional real inner-product space.
  This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals List ClassicalDescription
  ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q2096184_set (A : Type) : Type := A -> Prop.

Definition q2096184_empty {A : Type} : q2096184_set A :=
  fun _ => False.

Definition q2096184_full {A : Type} : q2096184_set A :=
  fun _ => True.

Definition q2096184_complement {A : Type}
    (E : q2096184_set A) : q2096184_set A :=
  fun x => ~ E x.

Definition q2096184_countable_union {A : Type}
    (E : nat -> q2096184_set A) : q2096184_set A :=
  fun x => exists n : nat, E n x.

Definition q2096184_same_set {A : Type}
    (E F : q2096184_set A) : Prop :=
  forall x : A, E x <-> F x.

Definition q2096184_disjoint {A : Type}
    (E F : q2096184_set A) : Prop :=
  forall x : A, ~ (E x /\ F x).

Definition q2096184_pairwise_disjoint {A : Type}
    (E : nat -> q2096184_set A) : Prop :=
  forall i j : nat, i <> j -> q2096184_disjoint (E i) (E j).

Definition q2096184_sigma_class {A : Type}
    (C : q2096184_set (q2096184_set A)) : Prop :=
  C q2096184_empty /\
  (forall E F : q2096184_set A,
    q2096184_same_set E F ->
    C E ->
    C F) /\
  (forall E : q2096184_set A,
    C E -> C (q2096184_complement E)) /\
  (forall E : nat -> q2096184_set A,
    (forall n : nat, C (E n)) ->
    C (q2096184_countable_union E)).

Inductive q2096184_ennreal : Type :=
| q2096184_ennreal_finite :
    forall value : R, 0 <= value -> q2096184_ennreal
| q2096184_ennreal_infinity : q2096184_ennreal.

Arguments q2096184_ennreal_finite value nonnegative : clear implicits.

Definition q2096184_ennreal_zero : q2096184_ennreal :=
  q2096184_ennreal_finite 0 (Rle_refl 0).

Definition q2096184_ennreal_eq
    (x y : q2096184_ennreal) : Prop :=
  match x, y with
  | q2096184_ennreal_finite a _,
    q2096184_ennreal_finite b _ => a = b
  | q2096184_ennreal_infinity,
    q2096184_ennreal_infinity => True
  | _, _ => False
  end.

Definition q2096184_ennreal_le
    (x y : q2096184_ennreal) : Prop :=
  match x, y with
  | q2096184_ennreal_finite a _,
    q2096184_ennreal_finite b _ => a <= b
  | q2096184_ennreal_finite _ _,
    q2096184_ennreal_infinity => True
  | q2096184_ennreal_infinity,
    q2096184_ennreal_finite _ _ => False
  | q2096184_ennreal_infinity,
    q2096184_ennreal_infinity => True
  end.

Definition q2096184_ennreal_add
    (x y : q2096184_ennreal) : q2096184_ennreal :=
  match x, y with
  | q2096184_ennreal_finite a ha,
    q2096184_ennreal_finite b hb =>
      q2096184_ennreal_finite
        (a + b) (Rplus_le_le_0_compat a b ha hb)
  | _, _ => q2096184_ennreal_infinity
  end.

Definition q2096184_ennreal_mul
    (x y : q2096184_ennreal) : q2096184_ennreal :=
  match x, y with
  | q2096184_ennreal_finite a ha,
    q2096184_ennreal_finite b hb =>
      q2096184_ennreal_finite
        (a * b) (Rmult_le_pos a b ha hb)
  | q2096184_ennreal_finite a _, q2096184_ennreal_infinity
  | q2096184_ennreal_infinity, q2096184_ennreal_finite a _ =>
      if Req_EM_T a 0
      then q2096184_ennreal_zero
      else q2096184_ennreal_infinity
  | q2096184_ennreal_infinity, q2096184_ennreal_infinity =>
      q2096184_ennreal_infinity
  end.

Fixpoint q2096184_ennreal_partial_sum
    (u : nat -> q2096184_ennreal)
    (n : nat) : q2096184_ennreal :=
  match n with
  | O => q2096184_ennreal_zero
  | S k =>
      q2096184_ennreal_add
        (q2096184_ennreal_partial_sum u k) (u k)
  end.

Definition q2096184_ennreal_supremum
    (values : q2096184_ennreal -> Prop)
    (bound : q2096184_ennreal) : Prop :=
  (forall value : q2096184_ennreal,
      values value -> q2096184_ennreal_le value bound) /\
  (forall upper : q2096184_ennreal,
      (forall value : q2096184_ennreal,
        values value -> q2096184_ennreal_le value upper) ->
      q2096184_ennreal_le bound upper).

Definition q2096184_ennreal_series_sum
    (u : nat -> q2096184_ennreal)
    (sum : q2096184_ennreal) : Prop :=
  q2096184_ennreal_supremum
    (fun value =>
      exists n : nat,
        q2096184_ennreal_eq value
          (q2096184_ennreal_partial_sum u n))
    sum.

Definition q2096184_ennreal_represents
    (x : q2096184_ennreal) (value : R) : Prop :=
  exists nonnegative : 0 <= value,
    q2096184_ennreal_eq x
      (q2096184_ennreal_finite value nonnegative).

Definition q2096184_ennreal_finite_value
    (x : q2096184_ennreal) : Prop :=
  exists value : R, q2096184_ennreal_represents x value.

Record q2096184_measure_space (A : Type) : Type := {
  q2096184_measurable : q2096184_set A -> Prop;
  q2096184_measurable_extensional :
    forall E F : q2096184_set A,
      q2096184_same_set E F ->
      (q2096184_measurable E <-> q2096184_measurable F);
  q2096184_measurable_empty :
    q2096184_measurable q2096184_empty;
  q2096184_measurable_complement :
    forall E : q2096184_set A,
      q2096184_measurable E ->
      q2096184_measurable (q2096184_complement E);
  q2096184_measurable_countable_union :
    forall E : nat -> q2096184_set A,
      (forall n : nat, q2096184_measurable (E n)) ->
      q2096184_measurable (q2096184_countable_union E);
  q2096184_measure : q2096184_set A -> q2096184_ennreal;
  q2096184_measure_extensional :
    forall E F : q2096184_set A,
      q2096184_same_set E F ->
      q2096184_ennreal_eq
        (q2096184_measure E) (q2096184_measure F);
  q2096184_measure_empty :
    q2096184_ennreal_eq
      (q2096184_measure q2096184_empty)
      q2096184_ennreal_zero;
  q2096184_measure_countable_additive :
    forall E : nat -> q2096184_set A,
      (forall n : nat, q2096184_measurable (E n)) ->
      q2096184_pairwise_disjoint E ->
      q2096184_ennreal_series_sum
        (fun n => q2096184_measure (E n))
        (q2096184_measure (q2096184_countable_union E))
}.

Arguments q2096184_measurable {A} _ _.
Arguments q2096184_measure {A} _ _.

Definition q2096184_almost_everywhere {A : Type}
    (mu : q2096184_measure_space A)
    (P : A -> Prop) : Prop :=
  exists null_set : q2096184_set A,
    q2096184_measurable mu null_set /\
    q2096184_ennreal_eq
      (q2096184_measure mu null_set)
      q2096184_ennreal_zero /\
    forall x : A, ~ P x -> null_set x.

Record q2096184_normed_real_vector_space (G : Type) : Type := {
  q2096184_zero : G;
  q2096184_add : G -> G -> G;
  q2096184_neg : G -> G;
  q2096184_smul : R -> G -> G;
  q2096184_norm : G -> R;
  q2096184_add_assoc :
    forall x y z : G,
      q2096184_add x (q2096184_add y z) =
      q2096184_add (q2096184_add x y) z;
  q2096184_add_comm :
    forall x y : G, q2096184_add x y = q2096184_add y x;
  q2096184_add_zero :
    forall x : G, q2096184_add x q2096184_zero = x;
  q2096184_add_neg :
    forall x : G,
      q2096184_add x (q2096184_neg x) = q2096184_zero;
  q2096184_one_smul :
    forall x : G, q2096184_smul 1 x = x;
  q2096184_mul_smul :
    forall (a b : R) (x : G),
      q2096184_smul (a * b) x =
      q2096184_smul a (q2096184_smul b x);
  q2096184_add_smul :
    forall (a b : R) (x : G),
      q2096184_smul (a + b) x =
      q2096184_add (q2096184_smul a x) (q2096184_smul b x);
  q2096184_smul_add :
    forall (a : R) (x y : G),
      q2096184_smul a (q2096184_add x y) =
      q2096184_add (q2096184_smul a x) (q2096184_smul a y);
  q2096184_zero_smul :
    forall x : G, q2096184_smul 0 x = q2096184_zero;
  q2096184_smul_zero :
    forall a : R, q2096184_smul a q2096184_zero = q2096184_zero;
  q2096184_norm_nonnegative :
    forall x : G, 0 <= q2096184_norm x;
  q2096184_norm_eq_zero :
    forall x : G,
      q2096184_norm x = 0 <-> x = q2096184_zero;
  q2096184_norm_add_le :
    forall x y : G,
      q2096184_norm (q2096184_add x y) <=
      q2096184_norm x + q2096184_norm y;
  q2096184_norm_smul :
    forall (a : R) (x : G),
      q2096184_norm (q2096184_smul a x) =
      Rabs a * q2096184_norm x
}.

Arguments q2096184_zero {G} _.
Arguments q2096184_add {G} _ _ _.
Arguments q2096184_neg {G} _ _.
Arguments q2096184_smul {G} _ _ _.
Arguments q2096184_norm {G} _ _.

Definition q2096184_sub {G : Type}
    (V : q2096184_normed_real_vector_space G)
    (x y : G) : G :=
  q2096184_add V x (q2096184_neg V y).

Record q2096184_complex : Type := {
  q2096184_re : R;
  q2096184_im : R
}.

Definition q2096184_czero : q2096184_complex :=
  {| q2096184_re := 0; q2096184_im := 0 |}.

Definition q2096184_cone : q2096184_complex :=
  {| q2096184_re := 1; q2096184_im := 0 |}.

Definition q2096184_ci : q2096184_complex :=
  {| q2096184_re := 0; q2096184_im := 1 |}.

Definition q2096184_cadd
    (z w : q2096184_complex) : q2096184_complex :=
  {| q2096184_re := q2096184_re z + q2096184_re w;
     q2096184_im := q2096184_im z + q2096184_im w |}.

Definition q2096184_cneg
    (z : q2096184_complex) : q2096184_complex :=
  {| q2096184_re := - q2096184_re z;
     q2096184_im := - q2096184_im z |}.

Definition q2096184_csub
    (z w : q2096184_complex) : q2096184_complex :=
  q2096184_cadd z (q2096184_cneg w).

Definition q2096184_cmul
    (z w : q2096184_complex) : q2096184_complex :=
  {| q2096184_re :=
       q2096184_re z * q2096184_re w -
       q2096184_im z * q2096184_im w;
     q2096184_im :=
       q2096184_re z * q2096184_im w +
       q2096184_im z * q2096184_re w |}.

Definition q2096184_real_to_complex (x : R) : q2096184_complex :=
  {| q2096184_re := x; q2096184_im := 0 |}.

Definition q2096184_cconj
    (z : q2096184_complex) : q2096184_complex :=
  {| q2096184_re := q2096184_re z;
     q2096184_im := - q2096184_im z |}.

Definition q2096184_complex_modulus (z : q2096184_complex) : R :=
  sqrt
    (q2096184_re z * q2096184_re z +
     q2096184_im z * q2096184_im z).

Definition q2096184_complex_exp (z : q2096184_complex) : q2096184_complex :=
  {| q2096184_re := exp (q2096184_re z) * cos (q2096184_im z);
     q2096184_im := exp (q2096184_re z) * sin (q2096184_im z) |}.

Record q2096184_complex_normed_space
    {E : Type}
    (V : q2096184_normed_real_vector_space E) : Type := {
  q2096184_csmul : q2096184_complex -> E -> E;
  q2096184_csmul_one :
    forall x : E, q2096184_csmul q2096184_cone x = x;
  q2096184_csmul_mul :
    forall (a b : q2096184_complex) (x : E),
      q2096184_csmul (q2096184_cmul a b) x =
      q2096184_csmul a (q2096184_csmul b x);
  q2096184_csmul_add_scalar :
    forall (a b : q2096184_complex) (x : E),
      q2096184_csmul (q2096184_cadd a b) x =
      q2096184_add V (q2096184_csmul a x) (q2096184_csmul b x);
  q2096184_csmul_add_vector :
    forall (a : q2096184_complex) (x y : E),
      q2096184_csmul a (q2096184_add V x y) =
      q2096184_add V (q2096184_csmul a x) (q2096184_csmul a y);
  q2096184_csmul_real :
    forall (a : R) (x : E),
      q2096184_csmul (q2096184_real_to_complex a) x =
      q2096184_smul V a x;
  q2096184_norm_csmul :
    forall (a : q2096184_complex) (x : E),
      q2096184_norm V (q2096184_csmul a x) =
      q2096184_complex_modulus a * q2096184_norm V x
}.

Arguments q2096184_csmul {E V} _ _ _.

Record q2096184_complex_inner_product_space
    {E : Type}
    {N : q2096184_normed_real_vector_space E}
    (C : q2096184_complex_normed_space N) : Type := {
  q2096184_hinner : E -> E -> q2096184_complex;
  q2096184_hinner_add_left :
    forall x y z : E,
      q2096184_hinner (q2096184_add N x y) z =
      q2096184_cadd
        (q2096184_hinner x z) (q2096184_hinner y z);
  q2096184_hinner_add_right :
    forall x y z : E,
      q2096184_hinner x (q2096184_add N y z) =
      q2096184_cadd
        (q2096184_hinner x y) (q2096184_hinner x z);
  q2096184_hinner_smul_left :
    forall (a : q2096184_complex) (x y : E),
      q2096184_hinner (q2096184_csmul C a x) y =
      q2096184_cmul
        (q2096184_cconj a) (q2096184_hinner x y);
  q2096184_hinner_smul_right :
    forall (a : q2096184_complex) (x y : E),
      q2096184_hinner x (q2096184_csmul C a y) =
      q2096184_cmul a (q2096184_hinner x y);
  q2096184_hinner_conj_symm :
    forall x y : E,
      q2096184_hinner y x =
      q2096184_cconj (q2096184_hinner x y);
  q2096184_hinner_self :
    forall x : E,
      q2096184_im (q2096184_hinner x x) = 0 /\
      0 <= q2096184_re (q2096184_hinner x x) /\
      q2096184_re (q2096184_hinner x x) =
        q2096184_norm N x * q2096184_norm N x
}.

Arguments q2096184_hinner {E N C} _ _ _.

Record q2096184_real_inner_product_space
    {V : Type}
    (N : q2096184_normed_real_vector_space V) : Type := {
  q2096184_inner : V -> V -> R;
  q2096184_inner_add_left :
    forall x y z : V,
      q2096184_inner (q2096184_add N x y) z =
      q2096184_inner x z + q2096184_inner y z;
  q2096184_inner_smul_left :
    forall (a : R) (x y : V),
      q2096184_inner (q2096184_smul N a x) y =
      a * q2096184_inner x y;
  q2096184_inner_symmetric :
    forall x y : V, q2096184_inner x y = q2096184_inner y x;
  q2096184_inner_norm_sq :
    forall x : V,
      q2096184_inner x x = q2096184_norm N x * q2096184_norm N x
}.

Arguments q2096184_inner {V N} _ _ _.

Fixpoint q2096184_coordinate_sum
    {V : Type}
    (N : q2096184_normed_real_vector_space V)
    (n : nat) : (Fin.t n -> V) -> V :=
  match n as k return (Fin.t k -> V) -> V with
  | O => fun _ => q2096184_zero N
  | S k =>
      fun terms =>
        q2096184_add N
          (terms Fin.F1)
          (@q2096184_coordinate_sum V N k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q2096184_coordinate_sum {V} N n _.

Record q2096184_finite_dimensional
    {V : Type}
    {N : q2096184_normed_real_vector_space V}
    (H : q2096184_real_inner_product_space N) : Type := {
  q2096184_dimension : nat;
  q2096184_basis : Fin.t q2096184_dimension -> V;
  q2096184_coordinates : V -> Fin.t q2096184_dimension -> R;
  q2096184_coordinate_reconstruction :
    forall x : V,
      x =
      q2096184_coordinate_sum N q2096184_dimension
        (fun i =>
          q2096184_smul N
            (q2096184_coordinates x i) (q2096184_basis i));
  q2096184_coordinates_add :
    forall (x y : V) (i : Fin.t q2096184_dimension),
      q2096184_coordinates (q2096184_add N x y) i =
      q2096184_coordinates x i + q2096184_coordinates y i;
  q2096184_coordinates_smul :
    forall (a : R) (x : V) (i : Fin.t q2096184_dimension),
      q2096184_coordinates (q2096184_smul N a x) i =
      a * q2096184_coordinates x i;
  q2096184_basis_orthonormal :
    forall i j : Fin.t q2096184_dimension,
      q2096184_inner H (q2096184_basis i) (q2096184_basis j) =
      if Fin.eq_dec i j then 1 else 0
}.

Arguments q2096184_dimension {V N H} _.
Arguments q2096184_basis {V N H} _ _.
Arguments q2096184_coordinates {V N H} _ _ _.

Definition q2096184_open {V : Type}
    (N : q2096184_normed_real_vector_space V)
    (U : q2096184_set V) : Prop :=
  forall x : V,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : V,
        q2096184_norm N (q2096184_sub N y x) < radius ->
        U y.

Definition q2096184_borel_set {V : Type}
    (N : q2096184_normed_real_vector_space V)
    (S : q2096184_set V) : Prop :=
  forall classes : q2096184_set (q2096184_set V),
    q2096184_sigma_class classes ->
    (forall U : q2096184_set V, q2096184_open N U -> classes U) ->
    classes S.

Definition q2096184_unit_coordinate_cube
    {V : Type}
    {N : q2096184_normed_real_vector_space V}
    {H : q2096184_real_inner_product_space N}
    (D : q2096184_finite_dimensional H) : q2096184_set V :=
  fun x =>
    forall i : Fin.t (q2096184_dimension D),
      0 < q2096184_coordinates D x i <= 1.

Definition q2096184_is_euclidean_lebesgue_measure
    {V : Type}
    {N : q2096184_normed_real_vector_space V}
    {H : q2096184_real_inner_product_space N}
    (D : q2096184_finite_dimensional H)
    (mu : q2096184_measure_space V) : Prop :=
  (forall S : q2096184_set V,
      q2096184_measurable mu S <-> q2096184_borel_set N S) /\
  (forall (a : V) (S : q2096184_set V),
      q2096184_ennreal_eq
        (q2096184_measure mu
          (fun x => S (q2096184_add N a x)))
        (q2096184_measure mu S)) /\
  q2096184_ennreal_eq
    (q2096184_measure mu (q2096184_unit_coordinate_cube D))
    (q2096184_ennreal_finite 1 Rle_0_1).

Definition q2096184_vector_sequence_converges {G : Type}
    (V : q2096184_normed_real_vector_space G)
    (u : nat -> G) (limit : G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q2096184_norm V
          (q2096184_sub V (u n) limit) < epsilon.

Definition q2096184_vector_sequence_cauchy {G : Type}
    (V : q2096184_normed_real_vector_space G)
    (u : nat -> G) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q2096184_norm V
          (q2096184_sub V (u m) (u n)) < epsilon.

Definition q2096184_complete {G : Type}
    (V : q2096184_normed_real_vector_space G) : Prop :=
  forall u : nat -> G,
    q2096184_vector_sequence_cauchy V u ->
    exists limit : G,
      q2096184_vector_sequence_converges V u limit.

Definition q2096184_real_sequence_converges
    (u : nat -> R) (limit : R) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        Rabs (u n - limit) < epsilon.

Definition q2096184_finite_partition {A : Type}
    (mu : q2096184_measure_space A)
    (k : nat) (cells : nat -> q2096184_set A) : Prop :=
  (0 < k)%nat /\
  (forall i : nat,
    (i < k)%nat -> q2096184_measurable mu (cells i)) /\
  (forall i j : nat,
    (i < k)%nat ->
    (j < k)%nat ->
    i <> j ->
    q2096184_disjoint (cells i) (cells j)) /\
  (forall x : A,
    exists i : nat, (i < k)%nat /\ cells i x).

Definition q2096184_measurable_simple {A G : Type}
    (mu : q2096184_measure_space A)
    (s : A -> G) : Prop :=
  exists (k : nat) (coefficients : nat -> G)
         (cells : nat -> q2096184_set A),
    q2096184_finite_partition mu k cells /\
    forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i.

Definition q2096184_ae_strongly_measurable {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (f : A -> G) : Prop :=
  exists approximants : nat -> A -> G,
    (forall n : nat,
      q2096184_measurable_simple mu (approximants n)) /\
    q2096184_almost_everywhere mu
      (fun x =>
        q2096184_vector_sequence_converges V
          (fun n => approximants n x) (f x)).

Record q2096184_nonnegative_real : Type := {
  q2096184_nnreal_value : R;
  q2096184_nnreal_nonnegative : 0 <= q2096184_nnreal_value
}.

Definition q2096184_ennreal_of_nonnegative
    (x : q2096184_nonnegative_real) : q2096184_ennreal :=
  q2096184_ennreal_finite
    (q2096184_nnreal_value x)
    (q2096184_nnreal_nonnegative x).

Definition q2096184_simple_lintegral_below {A : Type}
    (mu : q2096184_measure_space A)
    (f : A -> q2096184_ennreal)
    (value : q2096184_ennreal) : Prop :=
  exists (k : nat)
         (coefficients : nat -> q2096184_nonnegative_real)
         (cells : nat -> q2096184_set A),
    q2096184_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      q2096184_ennreal_le
        (q2096184_ennreal_of_nonnegative (coefficients i))
        (f x)) /\
    q2096184_ennreal_eq value
      (q2096184_ennreal_partial_sum
        (fun i =>
          q2096184_ennreal_mul
            (q2096184_ennreal_of_nonnegative (coefficients i))
            (q2096184_measure mu (cells i)))
        k).

Definition q2096184_lintegral_has_value {A : Type}
    (mu : q2096184_measure_space A)
    (f : A -> q2096184_ennreal)
    (value : q2096184_ennreal) : Prop :=
  q2096184_ennreal_supremum
    (q2096184_simple_lintegral_below mu f) value.

Definition q2096184_norm_ennreal {G : Type}
    (V : q2096184_normed_real_vector_space G)
    (x : G) : q2096184_ennreal :=
  q2096184_ennreal_finite
    (q2096184_norm V x)
    (q2096184_norm_nonnegative V x).

Definition q2096184_integrable {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (f : A -> G) : Prop :=
  q2096184_ae_strongly_measurable V mu f /\
  exists value : q2096184_ennreal,
    q2096184_lintegral_has_value mu
      (fun x => q2096184_norm_ennreal V (f x)) value /\
    q2096184_ennreal_finite_value value.

Fixpoint q2096184_vector_sum {G : Type}
    (V : q2096184_normed_real_vector_space G)
    (u : nat -> G) (n : nat) : G :=
  match n with
  | O => q2096184_zero V
  | S k =>
      q2096184_add V
        (q2096184_vector_sum V u k) (u k)
  end.

Definition q2096184_weighted_cell_value {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (cell : q2096184_set A)
    (coefficient value : G) : Prop :=
  (coefficient = q2096184_zero V /\
    value = q2096184_zero V) \/
  exists mass : R,
    q2096184_ennreal_represents
      (q2096184_measure mu cell) mass /\
    value = q2096184_smul V mass coefficient.

Definition q2096184_simple_integral_has_value {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (s : A -> G) (value : G) : Prop :=
  exists (k : nat) (coefficients terms : nat -> G)
         (cells : nat -> q2096184_set A),
    q2096184_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q2096184_weighted_cell_value
        V mu (cells i) (coefficients i) (terms i)) /\
    value = q2096184_vector_sum V terms k.

Definition q2096184_l1_approximates {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (approximants : nat -> A -> G)
    (f : A -> G) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q2096184_ennreal,
        q2096184_lintegral_has_value mu
          (fun x =>
            q2096184_norm_ennreal V
              (q2096184_sub V (approximants n x) (f x)))
          integral_error /\
        q2096184_ennreal_represents
          integral_error (errors n)) /\
    q2096184_real_sequence_converges errors 0.

Definition q2096184_standard_bochner_integral_value {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (f : A -> G) (value : G) : Prop :=
  exists (approximants : nat -> A -> G)
         (integrals : nat -> G),
    (forall n : nat,
      q2096184_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q2096184_simple_integral_has_value
        V mu (approximants n) (integrals n)) /\
    q2096184_l1_approximates V mu approximants f /\
    q2096184_vector_sequence_converges V integrals value.

Definition q2096184_bochner_integral {A G : Type}
    (V : q2096184_normed_real_vector_space G)
    (mu : q2096184_measure_space A)
    (f : A -> G) : G :=
  match excluded_middle_informative
          (exists value : G,
            q2096184_standard_bochner_integral_value V mu f value) with
  | left _ =>
      epsilon (inhabits (q2096184_zero V))
        (fun value : G =>
          q2096184_standard_bochner_integral_value V mu f value)
  | right _ => q2096184_zero V
  end.

Definition q2096184_continuous_at
    {V E : Type}
    (NV : q2096184_normed_real_vector_space V)
    (NE : q2096184_normed_real_vector_space E)
    (f : V -> E) (v : V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall w : V,
        q2096184_norm NV (q2096184_sub NV w v) < delta ->
        q2096184_norm NE
          (q2096184_sub NE (f w) (f v)) < epsilon.

Definition q2096184_continuous
    {V E : Type}
    (NV : q2096184_normed_real_vector_space V)
    (NE : q2096184_normed_real_vector_space E)
    (f : V -> E) : Prop :=
  forall v : V, q2096184_continuous_at NV NE f v.

Definition q2096184_has_directional_derivative
    {V E : Type}
    (NV : q2096184_normed_real_vector_space V)
    (NE : q2096184_normed_real_vector_space E)
    (f : V -> E) (direction : V)
    (derivative : V -> E) : Prop :=
  forall (x : V) (epsilon : R),
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall t : R,
        Rabs t < delta ->
        q2096184_norm NE
          (q2096184_sub NE
            (q2096184_sub NE
              (f (q2096184_add NV x
                (q2096184_smul NV t direction)))
              (f x))
            (q2096184_smul NE t (derivative x)))
        <= epsilon * Rabs t.

Definition q2096184_schwartz
    {V E : Type}
    (NV : q2096184_normed_real_vector_space V)
    (VH : q2096184_real_inner_product_space NV)
    (D : q2096184_finite_dimensional VH)
    (NE : q2096184_normed_real_vector_space E)
    (f : V -> E) : Prop :=
  exists derivatives :
      list (Fin.t (q2096184_dimension D)) -> V -> E,
    derivatives nil = f /\
    (forall (directions : list (Fin.t (q2096184_dimension D)))
            (i : Fin.t (q2096184_dimension D)),
      q2096184_has_directional_derivative NV NE
        (derivatives directions)
        (q2096184_basis D i)
        (derivatives (cons i directions))) /\
    (forall directions,
      q2096184_continuous NV NE (derivatives directions)) /\
    forall (directions : list (Fin.t (q2096184_dimension D)))
           (power : nat),
      exists bound : R,
        0 <= bound /\
        forall x : V,
          (1 + q2096184_norm NV x) ^ power *
            q2096184_norm NE (derivatives directions x)
          <= bound.

Fixpoint q2096184_complex_sum
    (u : nat -> q2096184_complex)
    (n : nat) : q2096184_complex :=
  match n with
  | O => q2096184_czero
  | S k =>
      q2096184_cadd
        (q2096184_complex_sum u k) (u k)
  end.

Definition q2096184_complex_sequence_converges
    (u : nat -> q2096184_complex)
    (limit : q2096184_complex) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q2096184_complex_modulus
          (q2096184_csub (u n) limit) < epsilon.

Definition q2096184_complex_norm_ennreal
    (z : q2096184_complex) : q2096184_ennreal :=
  q2096184_ennreal_finite
    (q2096184_complex_modulus z)
    (sqrt_pos
      (q2096184_re z * q2096184_re z +
       q2096184_im z * q2096184_im z)).

Definition q2096184_complex_weighted_cell_value
    {A : Type}
    (mu : q2096184_measure_space A)
    (cell : q2096184_set A)
    (coefficient value : q2096184_complex) : Prop :=
  (coefficient = q2096184_czero /\
    value = q2096184_czero) \/
  exists mass : R,
    q2096184_ennreal_represents
      (q2096184_measure mu cell) mass /\
    value =
      q2096184_cmul
        (q2096184_real_to_complex mass) coefficient.

Definition q2096184_complex_simple_integral_has_value
    {A : Type}
    (mu : q2096184_measure_space A)
    (s : A -> q2096184_complex)
    (value : q2096184_complex) : Prop :=
  exists (k : nat)
         (coefficients terms : nat -> q2096184_complex)
         (cells : nat -> q2096184_set A),
    q2096184_finite_partition mu k cells /\
    (forall (x : A) (i : nat),
      (i < k)%nat ->
      cells i x ->
      s x = coefficients i) /\
    (forall i : nat,
      (i < k)%nat ->
      q2096184_complex_weighted_cell_value
        mu (cells i) (coefficients i) (terms i)) /\
    value = q2096184_complex_sum terms k.

Definition q2096184_complex_l1_approximates
    {A : Type}
    (mu : q2096184_measure_space A)
    (approximants : nat -> A -> q2096184_complex)
    (f : A -> q2096184_complex) : Prop :=
  exists errors : nat -> R,
    (forall n : nat,
      exists integral_error : q2096184_ennreal,
        q2096184_lintegral_has_value mu
          (fun x =>
            q2096184_complex_norm_ennreal
              (q2096184_csub (approximants n x) (f x)))
          integral_error /\
        q2096184_ennreal_represents
          integral_error (errors n)) /\
    q2096184_real_sequence_converges errors 0.

Definition q2096184_standard_complex_bochner_integral_value
    {A : Type}
    (mu : q2096184_measure_space A)
    (f : A -> q2096184_complex)
    (value : q2096184_complex) : Prop :=
  exists (approximants : nat -> A -> q2096184_complex)
         (integrals : nat -> q2096184_complex),
    (forall n : nat,
      q2096184_measurable_simple mu (approximants n)) /\
    (forall n : nat,
      q2096184_complex_simple_integral_has_value
        mu (approximants n) (integrals n)) /\
    q2096184_complex_l1_approximates mu approximants f /\
    q2096184_complex_sequence_converges integrals value.

Definition q2096184_complex_bochner_integral
    {A : Type}
    (mu : q2096184_measure_space A)
    (f : A -> q2096184_complex) : q2096184_complex :=
  match excluded_middle_informative
          (exists value : q2096184_complex,
            q2096184_standard_complex_bochner_integral_value
              mu f value) with
  | left _ =>
      epsilon (inhabits q2096184_czero)
        (fun value : q2096184_complex =>
          q2096184_standard_complex_bochner_integral_value
            mu f value)
  | right _ => q2096184_czero
  end.

Definition q2096184_fourier_character (t : R) : q2096184_complex :=
  q2096184_complex_exp
    (q2096184_cmul
      (q2096184_real_to_complex (- (2 * PI * t)))
      q2096184_ci).

Definition q2096184_fourier_transform
    {V E : Type}
    {NV : q2096184_normed_real_vector_space V}
    (H : q2096184_real_inner_product_space NV)
    {NE : q2096184_normed_real_vector_space E}
    (CE : q2096184_complex_normed_space NE)
    (mu : q2096184_measure_space V)
    (f : V -> E) : V -> E :=
  fun w =>
    q2096184_bochner_integral NE mu
      (fun x =>
        q2096184_csmul CE
          (q2096184_fourier_character
            (q2096184_inner H x w))
          (f x)).

Theorem SchwartzMap_integral_inner_fourier_fourier :
  forall (V Hilbert : Type)
         (NV : q2096184_normed_real_vector_space V)
         (VH : q2096184_real_inner_product_space NV)
         (D : q2096184_finite_dimensional VH)
         (NH : q2096184_normed_real_vector_space Hilbert)
         (CH : q2096184_complex_normed_space NH)
         (IH : q2096184_complex_inner_product_space CH)
         (mu : q2096184_measure_space V)
         (f g : V -> Hilbert),
    q2096184_is_euclidean_lebesgue_measure D mu ->
    q2096184_complete NH ->
    @q2096184_schwartz V Hilbert NV VH D NH f ->
    @q2096184_schwartz V Hilbert NV VH D NH g ->
    q2096184_complex_bochner_integral mu
      (fun xi =>
        q2096184_hinner IH
          (q2096184_fourier_transform VH CH mu f xi)
          (q2096184_fourier_transform VH CH mu g xi))
    =
    q2096184_complex_bochner_integral mu
      (fun x => q2096184_hinner IH (f x) (g x)).
Admitted.
