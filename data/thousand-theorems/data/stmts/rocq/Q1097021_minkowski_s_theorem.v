(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1097021
  (thousand-theorems__rocq__Q1097021), "Minkowski's theorem": a convex
  origin-symmetric set whose Haar measure is sufficiently large relative to
  a fundamental domain contains a nonzero point of the countable lattice.
  This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals Arith List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1097021_set (A : Type) : Type := A -> Prop.

Definition q1097021_empty {A : Type} : q1097021_set A :=
  fun _ => False.

Definition q1097021_complement {A : Type}
    (S : q1097021_set A) : q1097021_set A :=
  fun x => ~ S x.

Definition q1097021_countable_union {A : Type}
    (S : nat -> q1097021_set A) : q1097021_set A :=
  fun x => exists n : nat, S n x.

Definition q1097021_same_set {A : Type}
    (S T : q1097021_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q1097021_intersection {A : Type}
    (S T : q1097021_set A) : q1097021_set A :=
  fun x => S x /\ T x.

Definition q1097021_symmetric_difference {A : Type}
    (S T : q1097021_set A) : q1097021_set A :=
  fun x => (S x /\ ~ T x) \/ (T x /\ ~ S x).

Record q1097021_normed_real_vector_space (E : Type) : Type := {
  q1097021_zero : E;
  q1097021_add : E -> E -> E;
  q1097021_neg : E -> E;
  q1097021_smul : R -> E -> E;
  q1097021_norm : E -> R;
  q1097021_add_assoc :
    forall x y z : E,
      q1097021_add x (q1097021_add y z) =
      q1097021_add (q1097021_add x y) z;
  q1097021_add_comm :
    forall x y : E, q1097021_add x y = q1097021_add y x;
  q1097021_add_zero :
    forall x : E, q1097021_add x q1097021_zero = x;
  q1097021_add_neg :
    forall x : E,
      q1097021_add x (q1097021_neg x) = q1097021_zero;
  q1097021_one_smul :
    forall x : E, q1097021_smul 1 x = x;
  q1097021_mul_smul :
    forall (a b : R) (x : E),
      q1097021_smul (a * b) x =
      q1097021_smul a (q1097021_smul b x);
  q1097021_add_smul :
    forall (a b : R) (x : E),
      q1097021_smul (a + b) x =
      q1097021_add (q1097021_smul a x) (q1097021_smul b x);
  q1097021_smul_add :
    forall (a : R) (x y : E),
      q1097021_smul a (q1097021_add x y) =
      q1097021_add (q1097021_smul a x) (q1097021_smul a y);
  q1097021_norm_nonnegative :
    forall x : E, 0 <= q1097021_norm x;
  q1097021_norm_eq_zero :
    forall x : E,
      q1097021_norm x = 0 <-> x = q1097021_zero;
  q1097021_norm_add_le :
    forall x y : E,
      q1097021_norm (q1097021_add x y) <=
      q1097021_norm x + q1097021_norm y;
  q1097021_norm_smul :
    forall (a : R) (x : E),
      q1097021_norm (q1097021_smul a x) =
      Rabs a * q1097021_norm x
}.

Arguments q1097021_zero {E} _.
Arguments q1097021_add {E} _ _ _.
Arguments q1097021_neg {E} _ _.
Arguments q1097021_smul {E} _ _ _.
Arguments q1097021_norm {E} _ _.

Definition q1097021_sub {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (x y : E) : E :=
  q1097021_add V x (q1097021_neg V y).

Fixpoint q1097021_vector_sum
    {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (n : nat) : (Fin.t n -> E) -> E :=
  match n as k return (Fin.t k -> E) -> E with
  | O => fun _ => q1097021_zero V
  | S k =>
      fun terms =>
        q1097021_add V
          (terms Fin.F1)
          (@q1097021_vector_sum E V k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1097021_vector_sum {E} V n _.

Record q1097021_finite_dimensional
    {E : Type}
    (V : q1097021_normed_real_vector_space E) : Type := {
  q1097021_dimension : nat;
  q1097021_basis : Fin.t q1097021_dimension -> E;
  q1097021_basis_spans :
    forall x : E,
      exists coefficients : Fin.t q1097021_dimension -> R,
        x =
          q1097021_vector_sum V q1097021_dimension
            (fun i =>
              q1097021_smul V
                (coefficients i) (q1097021_basis i));
  q1097021_basis_independent :
    forall coefficients : Fin.t q1097021_dimension -> R,
      q1097021_vector_sum V q1097021_dimension
        (fun i =>
          q1097021_smul V
            (coefficients i) (q1097021_basis i)) =
        q1097021_zero V ->
      forall i : Fin.t q1097021_dimension,
        coefficients i = 0
}.

Arguments q1097021_dimension {E V} _.

Definition q1097021_dist {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (x y : E) : R :=
  q1097021_norm V (q1097021_sub V x y).

Definition q1097021_open {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (U : q1097021_set E) : Prop :=
  forall x : E,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : E,
        q1097021_dist V y x < radius ->
        U y.

Definition q1097021_sigma_class {A : Type}
    (C : q1097021_set (q1097021_set A)) : Prop :=
  C q1097021_empty /\
  (forall S : q1097021_set A,
    C S -> C (q1097021_complement S)) /\
  (forall S : nat -> q1097021_set A,
    (forall n : nat, C (S n)) ->
    C (q1097021_countable_union S)).

Definition q1097021_borel_set {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (S : q1097021_set E) : Prop :=
  forall C : q1097021_set (q1097021_set E),
    q1097021_sigma_class C ->
    (forall U : q1097021_set E,
      q1097021_open V U -> C U) ->
    C S.

Definition q1097021_compact {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (K : q1097021_set E) : Prop :=
  forall cover : q1097021_set (q1097021_set E),
    (forall U : q1097021_set E,
      cover U -> q1097021_open V U) ->
    (forall x : E,
      K x ->
      exists U : q1097021_set E, cover U /\ U x) ->
    exists finite_cover : list (q1097021_set E),
      Forall cover finite_cover /\
      forall x : E,
        K x ->
        exists U : q1097021_set E,
          In U finite_cover /\ U x.

Inductive q1097021_ennreal : Type :=
| q1097021_ennreal_finite : R -> q1097021_ennreal
| q1097021_ennreal_infinity : q1097021_ennreal.

Definition q1097021_ennreal_valid
    (x : q1097021_ennreal) : Prop :=
  match x with
  | q1097021_ennreal_finite value => 0 <= value
  | q1097021_ennreal_infinity => True
  end.

Definition q1097021_ennreal_zero : q1097021_ennreal :=
  q1097021_ennreal_finite 0.

Definition q1097021_ennreal_add
    (x y : q1097021_ennreal) : q1097021_ennreal :=
  match x, y with
  | q1097021_ennreal_finite a, q1097021_ennreal_finite b =>
      q1097021_ennreal_finite (a + b)
  | _, _ => q1097021_ennreal_infinity
  end.

Definition q1097021_ennreal_mul
    (x y : q1097021_ennreal) : q1097021_ennreal :=
  match x, y with
  | q1097021_ennreal_finite a, q1097021_ennreal_finite b =>
      q1097021_ennreal_finite (a * b)
  | q1097021_ennreal_finite a, q1097021_ennreal_infinity
  | q1097021_ennreal_infinity, q1097021_ennreal_finite a =>
      if Req_EM_T a 0
      then q1097021_ennreal_zero
      else q1097021_ennreal_infinity
  | q1097021_ennreal_infinity, q1097021_ennreal_infinity =>
      q1097021_ennreal_infinity
  end.

Definition q1097021_ennreal_le
    (x y : q1097021_ennreal) : Prop :=
  match x, y with
  | q1097021_ennreal_finite a, q1097021_ennreal_finite b => a <= b
  | q1097021_ennreal_finite _, q1097021_ennreal_infinity => True
  | q1097021_ennreal_infinity, q1097021_ennreal_finite _ => False
  | q1097021_ennreal_infinity, q1097021_ennreal_infinity => True
  end.

Definition q1097021_ennreal_lt
    (x y : q1097021_ennreal) : Prop :=
  match x, y with
  | q1097021_ennreal_finite a, q1097021_ennreal_finite b => a < b
  | q1097021_ennreal_finite _, q1097021_ennreal_infinity => True
  | _, _ => False
  end.

Fixpoint q1097021_ennreal_partial_sum
    (u : nat -> q1097021_ennreal)
    (n : nat) : q1097021_ennreal :=
  match n with
  | O => q1097021_ennreal_zero
  | S k =>
      q1097021_ennreal_add
        (q1097021_ennreal_partial_sum u k) (u k)
  end.

Definition q1097021_ennreal_series_sum
    (u : nat -> q1097021_ennreal)
    (total : q1097021_ennreal) : Prop :=
  q1097021_ennreal_valid total /\
  (forall n : nat,
    q1097021_ennreal_le
      (q1097021_ennreal_partial_sum u n) total) /\
  forall upper : q1097021_ennreal,
    q1097021_ennreal_valid upper ->
    (forall n : nat,
      q1097021_ennreal_le
        (q1097021_ennreal_partial_sum u n) upper) ->
    q1097021_ennreal_le total upper.

Definition q1097021_pairwise_disjoint {A : Type}
    (S : nat -> q1097021_set A) : Prop :=
  forall i j : nat,
    i <> j ->
    forall x : A, ~ (S i x /\ S j x).

Record q1097021_borel_measure
    {E : Type}
    (V : q1097021_normed_real_vector_space E) : Type := {
  q1097021_measure :
    q1097021_set E -> q1097021_ennreal;
  q1097021_measure_valid :
    forall S : q1097021_set E,
      q1097021_ennreal_valid (q1097021_measure S);
  q1097021_measure_extensional :
    forall S T : q1097021_set E,
      q1097021_same_set S T ->
      q1097021_measure S = q1097021_measure T;
  q1097021_measure_empty :
    q1097021_measure q1097021_empty =
      q1097021_ennreal_zero;
  q1097021_measure_monotone :
    forall S T : q1097021_set E,
      (forall x : E, S x -> T x) ->
      q1097021_ennreal_le
        (q1097021_measure S) (q1097021_measure T);
  q1097021_measure_canonical_extension :
    forall (S : q1097021_set E)
           (lower : q1097021_ennreal),
      q1097021_ennreal_valid lower ->
      ((forall T : q1097021_set E,
          q1097021_borel_set V T ->
          (forall x : E, S x -> T x) ->
          q1097021_ennreal_le lower
            (q1097021_measure T)) <->
       q1097021_ennreal_le lower
         (q1097021_measure S));
  q1097021_measure_countable_subadditive :
    forall S : nat -> q1097021_set E,
      exists total : q1097021_ennreal,
        q1097021_ennreal_series_sum
          (fun n => q1097021_measure (S n)) total /\
        q1097021_ennreal_le
          (q1097021_measure (q1097021_countable_union S))
          total;
  q1097021_measure_countable_additive :
    forall S : nat -> q1097021_set E,
      (forall n : nat, q1097021_borel_set V (S n)) ->
      q1097021_pairwise_disjoint S ->
      exists total : q1097021_ennreal,
        q1097021_ennreal_series_sum
          (fun n => q1097021_measure (S n)) total /\
        q1097021_measure (q1097021_countable_union S) = total
}.

Arguments q1097021_measure {E V} _ _.

Definition q1097021_null_measurable {E : Type}
    {V : q1097021_normed_real_vector_space E}
    (mu : q1097021_borel_measure V)
    (S : q1097021_set E) : Prop :=
  exists T : q1097021_set E,
    q1097021_borel_set V T /\
    q1097021_measure mu
      (q1097021_symmetric_difference S T) =
      q1097021_ennreal_zero.

Record q1097021_add_haar_measure
    {E : Type}
    {V : q1097021_normed_real_vector_space E}
    (mu : q1097021_borel_measure V) : Prop := {
  q1097021_haar_left_invariant :
    forall (a : E) (S : q1097021_set E),
      q1097021_measure mu
        (fun x : E => S (q1097021_add V a x)) =
      q1097021_measure mu S;
  q1097021_haar_finite_on_compact :
    forall K : q1097021_set E,
      q1097021_compact V K ->
      q1097021_ennreal_lt
        (q1097021_measure mu K)
        q1097021_ennreal_infinity;
  q1097021_haar_positive_on_nonempty_open :
    forall U : q1097021_set E,
      q1097021_open V U ->
      (exists x : E, U x) ->
      q1097021_measure mu U <> q1097021_ennreal_zero
}.

Definition q1097021_add_subgroup {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (L : q1097021_set E) : Prop :=
  L (q1097021_zero V) /\
  (forall x y : E,
    L x -> L y -> L (q1097021_add V x y)) /\
  forall x : E,
    L x -> L (q1097021_neg V x).

Definition q1097021_countable_set {E : Type}
    (L : q1097021_set E) : Prop :=
  exists encode : E -> nat,
    forall x y : E,
      L x ->
      L y ->
      encode x = encode y ->
      x = y.

Definition q1097021_translate {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (a : E)
    (S : q1097021_set E) : q1097021_set E :=
  fun x : E =>
    exists y : E, S y /\ x = q1097021_add V a y.

Record q1097021_is_add_fundamental_domain
    {E : Type}
    {V : q1097021_normed_real_vector_space E}
    (mu : q1097021_borel_measure V)
    (L F : q1097021_set E) : Prop := {
  q1097021_fund_null_measurable :
    q1097021_null_measurable mu F;
  q1097021_fund_ae_covers :
    q1097021_measure mu
      (fun x : E =>
        ~ exists g : E,
          L g /\ q1097021_translate V g F x) =
      q1097021_ennreal_zero;
  q1097021_fund_ae_disjoint :
    forall g h : E,
      L g ->
      L h ->
      g <> h ->
      q1097021_measure mu
        (q1097021_intersection
          (q1097021_translate V g F)
          (q1097021_translate V h F)) =
        q1097021_ennreal_zero
}.

Definition q1097021_origin_symmetric {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (S : q1097021_set E) : Prop :=
  forall x : E,
    S x -> S (q1097021_neg V x).

Definition q1097021_convex {E : Type}
    (V : q1097021_normed_real_vector_space E)
    (S : q1097021_set E) : Prop :=
  forall (x y : E) (a b : R),
    S x ->
    S y ->
    0 <= a ->
    0 <= b ->
    a + b = 1 ->
    S
      (q1097021_add V
        (q1097021_smul V a x)
        (q1097021_smul V b y)).

Definition q1097021_two_pow
    (n : nat) : q1097021_ennreal :=
  q1097021_ennreal_finite (INR (Nat.pow 2 n)).

Theorem exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure :
  forall (E : Type)
         (V : q1097021_normed_real_vector_space E)
         (D : q1097021_finite_dimensional V)
         (mu : q1097021_borel_measure V)
         (L F S : q1097021_set E),
    q1097021_add_haar_measure mu ->
    q1097021_add_subgroup V L ->
    q1097021_countable_set L ->
    q1097021_is_add_fundamental_domain mu L F ->
    q1097021_origin_symmetric V S ->
    q1097021_convex V S ->
    q1097021_ennreal_lt
      (q1097021_ennreal_mul
        (q1097021_measure mu F)
        (q1097021_two_pow (q1097021_dimension D)))
      (q1097021_measure mu S) ->
    exists x : E,
      L x /\ x <> q1097021_zero V /\ S x.
Admitted.
