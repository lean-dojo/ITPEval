(*
  Statement-only formalization of Thousand Theorems corpus artifact Q132427
  (thousand-theorems__rocq__Q132427), "Rademacher's theorem": a Lipschitz map
  on a measurable subset of a finite-dimensional real normed vector space is
  Frechet differentiable within that subset almost everywhere for the
  restricted additive Haar measure. This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals Arith List.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q132427_set (A : Type) : Type := A -> Prop.

Definition q132427_empty {A : Type} : q132427_set A :=
  fun _ => False.

Definition q132427_complement {A : Type}
    (S : q132427_set A) : q132427_set A :=
  fun x => ~ S x.

Definition q132427_intersection {A : Type}
    (S T : q132427_set A) : q132427_set A :=
  fun x => S x /\ T x.

Definition q132427_countable_union {A : Type}
    (S : nat -> q132427_set A) : q132427_set A :=
  fun x => exists n : nat, S n x.

Definition q132427_same_set {A : Type}
    (S T : q132427_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q132427_pairwise_disjoint {A : Type}
    (S : nat -> q132427_set A) : Prop :=
  forall i j : nat,
    i <> j ->
    forall x : A, ~ (S i x /\ S j x).

Record q132427_normed_real_vector_space (E : Type) : Type := {
  q132427_zero : E;
  q132427_add : E -> E -> E;
  q132427_neg : E -> E;
  q132427_smul : R -> E -> E;
  q132427_norm : E -> R;
  q132427_add_assoc :
    forall x y z : E,
      q132427_add x (q132427_add y z) =
      q132427_add (q132427_add x y) z;
  q132427_add_comm :
    forall x y : E, q132427_add x y = q132427_add y x;
  q132427_add_zero :
    forall x : E, q132427_add x q132427_zero = x;
  q132427_add_neg :
    forall x : E, q132427_add x (q132427_neg x) = q132427_zero;
  q132427_one_smul :
    forall x : E, q132427_smul 1 x = x;
  q132427_mul_smul :
    forall (a b : R) (x : E),
      q132427_smul (a * b) x =
      q132427_smul a (q132427_smul b x);
  q132427_add_smul :
    forall (a b : R) (x : E),
      q132427_smul (a + b) x =
      q132427_add (q132427_smul a x) (q132427_smul b x);
  q132427_smul_add :
    forall (a : R) (x y : E),
      q132427_smul a (q132427_add x y) =
      q132427_add (q132427_smul a x) (q132427_smul a y);
  q132427_norm_nonnegative :
    forall x : E, 0 <= q132427_norm x;
  q132427_norm_eq_zero :
    forall x : E,
      q132427_norm x = 0 <-> x = q132427_zero;
  q132427_norm_add_le :
    forall x y : E,
      q132427_norm (q132427_add x y) <=
      q132427_norm x + q132427_norm y;
  q132427_norm_smul :
    forall (a : R) (x : E),
      q132427_norm (q132427_smul a x) =
      Rabs a * q132427_norm x
}.

Arguments q132427_zero {E} _.
Arguments q132427_add {E} _ _ _.
Arguments q132427_neg {E} _ _.
Arguments q132427_smul {E} _ _ _.
Arguments q132427_norm {E} _ _.

Definition q132427_sub {E : Type}
    (V : q132427_normed_real_vector_space E)
    (x y : E) : E :=
  q132427_add V x (q132427_neg V y).

Definition q132427_dist {E : Type}
    (V : q132427_normed_real_vector_space E)
    (x y : E) : R :=
  q132427_norm V (q132427_sub V x y).

Fixpoint q132427_vector_sum
    {E : Type}
    (V : q132427_normed_real_vector_space E)
    (n : nat) : (Fin.t n -> E) -> E :=
  match n as k return (Fin.t k -> E) -> E with
  | O => fun _ => q132427_zero V
  | S k =>
      fun terms =>
        q132427_add V
          (terms Fin.F1)
          (@q132427_vector_sum E V k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q132427_vector_sum {E} V n _.

Record q132427_finite_dimensional
    {E : Type}
    (V : q132427_normed_real_vector_space E) : Type := {
  q132427_dimension : nat;
  q132427_basis : Fin.t q132427_dimension -> E;
  q132427_basis_spans :
    forall x : E,
      exists coefficients : Fin.t q132427_dimension -> R,
        x =
          q132427_vector_sum V q132427_dimension
            (fun i =>
              q132427_smul V
                (coefficients i) (q132427_basis i));
  q132427_basis_independent :
    forall coefficients : Fin.t q132427_dimension -> R,
      q132427_vector_sum V q132427_dimension
        (fun i =>
          q132427_smul V
            (coefficients i) (q132427_basis i)) =
        q132427_zero V ->
      forall i : Fin.t q132427_dimension,
        coefficients i = 0
}.

Definition q132427_open {E : Type}
    (V : q132427_normed_real_vector_space E)
    (U : q132427_set E) : Prop :=
  forall x : E,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : E,
        q132427_dist V y x < radius ->
        U y.

Definition q132427_sigma_class {A : Type}
    (C : q132427_set (q132427_set A)) : Prop :=
  C q132427_empty /\
  (forall S T : q132427_set A,
    q132427_same_set S T -> C S -> C T) /\
  (forall S : q132427_set A,
    C S -> C (q132427_complement S)) /\
  (forall S : nat -> q132427_set A,
    (forall n : nat, C (S n)) ->
    C (q132427_countable_union S)).

Definition q132427_borel_set {E : Type}
    (V : q132427_normed_real_vector_space E)
    (S : q132427_set E) : Prop :=
  forall C : q132427_set (q132427_set E),
    q132427_sigma_class C ->
    (forall U : q132427_set E,
      q132427_open V U -> C U) ->
    C S.

Definition q132427_compact {E : Type}
    (V : q132427_normed_real_vector_space E)
    (K : q132427_set E) : Prop :=
  forall cover : q132427_set (q132427_set E),
    (forall U : q132427_set E,
      cover U -> q132427_open V U) ->
    (forall x : E,
      K x ->
      exists U : q132427_set E, cover U /\ U x) ->
    exists finite_cover : list (q132427_set E),
      Forall cover finite_cover /\
      forall x : E,
        K x ->
        exists U : q132427_set E,
          In U finite_cover /\ U x.

Inductive q132427_ennreal : Type :=
| q132427_ennreal_finite : R -> q132427_ennreal
| q132427_ennreal_infinity : q132427_ennreal.

Definition q132427_ennreal_valid
    (x : q132427_ennreal) : Prop :=
  match x with
  | q132427_ennreal_finite value => 0 <= value
  | q132427_ennreal_infinity => True
  end.

Definition q132427_ennreal_zero : q132427_ennreal :=
  q132427_ennreal_finite 0.

Definition q132427_ennreal_add
    (x y : q132427_ennreal) : q132427_ennreal :=
  match x, y with
  | q132427_ennreal_finite a, q132427_ennreal_finite b =>
      q132427_ennreal_finite (a + b)
  | _, _ => q132427_ennreal_infinity
  end.

Definition q132427_ennreal_le
    (x y : q132427_ennreal) : Prop :=
  match x, y with
  | q132427_ennreal_finite a, q132427_ennreal_finite b => a <= b
  | q132427_ennreal_finite _, q132427_ennreal_infinity => True
  | q132427_ennreal_infinity, q132427_ennreal_finite _ => False
  | q132427_ennreal_infinity, q132427_ennreal_infinity => True
  end.

Definition q132427_ennreal_lt
    (x y : q132427_ennreal) : Prop :=
  match x, y with
  | q132427_ennreal_finite a, q132427_ennreal_finite b => a < b
  | q132427_ennreal_finite _, q132427_ennreal_infinity => True
  | _, _ => False
  end.

Fixpoint q132427_ennreal_partial_sum
    (u : nat -> q132427_ennreal)
    (n : nat) : q132427_ennreal :=
  match n with
  | O => q132427_ennreal_zero
  | S k =>
      q132427_ennreal_add
        (q132427_ennreal_partial_sum u k) (u k)
  end.

Definition q132427_ennreal_series_sum
    (u : nat -> q132427_ennreal)
    (total : q132427_ennreal) : Prop :=
  q132427_ennreal_valid total /\
  (forall n : nat,
    q132427_ennreal_le
      (q132427_ennreal_partial_sum u n) total) /\
  forall upper : q132427_ennreal,
    q132427_ennreal_valid upper ->
    (forall n : nat,
      q132427_ennreal_le
        (q132427_ennreal_partial_sum u n) upper) ->
    q132427_ennreal_le total upper.

Record q132427_borel_measure
    {E : Type}
    (V : q132427_normed_real_vector_space E) : Type := {
  q132427_measure :
    q132427_set E -> q132427_ennreal;
  q132427_measure_valid :
    forall S : q132427_set E,
      q132427_ennreal_valid (q132427_measure S);
  q132427_measure_extensional :
    forall S T : q132427_set E,
      q132427_same_set S T ->
      q132427_measure S = q132427_measure T;
  q132427_measure_empty :
    q132427_measure q132427_empty =
      q132427_ennreal_zero;
  q132427_measure_monotone :
    forall S T : q132427_set E,
      (forall x : E, S x -> T x) ->
      q132427_ennreal_le
        (q132427_measure S) (q132427_measure T);
  q132427_measure_countable_subadditive :
    forall S : nat -> q132427_set E,
      exists total : q132427_ennreal,
        q132427_ennreal_series_sum
          (fun n => q132427_measure (S n)) total /\
        q132427_ennreal_le
          (q132427_measure (q132427_countable_union S))
          total;
  q132427_measure_caratheodory :
    forall S T : q132427_set E,
      q132427_borel_set V S ->
      q132427_measure T =
        q132427_ennreal_add
          (q132427_measure (q132427_intersection T S))
          (q132427_measure
            (q132427_intersection T
              (q132427_complement S)));
  q132427_measure_countable_additive :
    forall S : nat -> q132427_set E,
      (forall n : nat, q132427_borel_set V (S n)) ->
      q132427_pairwise_disjoint S ->
      exists total : q132427_ennreal,
        q132427_ennreal_series_sum
          (fun n => q132427_measure (S n)) total /\
        q132427_measure (q132427_countable_union S) = total
}.

Arguments q132427_measure {E V} _ _.

Record q132427_add_haar_measure
    {E : Type}
    {V : q132427_normed_real_vector_space E}
    (mu : q132427_borel_measure V) : Prop := {
  q132427_haar_left_invariant :
    forall (a : E) (S : q132427_set E),
      q132427_measure mu
        (fun x : E => S (q132427_add V a x)) =
      q132427_measure mu S;
  q132427_haar_finite_on_compact :
    forall K : q132427_set E,
      q132427_compact V K ->
      q132427_ennreal_lt
        (q132427_measure mu K)
        q132427_ennreal_infinity;
  q132427_haar_positive_on_nonempty_open :
    forall U : q132427_set E,
      q132427_open V U ->
      (exists x : E, U x) ->
      q132427_measure mu U <> q132427_ennreal_zero
}.

Record q132427_nonnegative_real : Type := {
  q132427_nonnegative_value : R;
  q132427_value_nonnegative : 0 <= q132427_nonnegative_value
}.

Definition q132427_lipschitz_on_with
    {E F : Type}
    (VE : q132427_normed_real_vector_space E)
    (VF : q132427_normed_real_vector_space F)
    (C : q132427_nonnegative_real)
    (f : E -> F)
    (s : q132427_set E) : Prop :=
  forall x y : E,
    s x ->
    s y ->
    q132427_norm VF (q132427_sub VF (f x) (f y)) <=
      q132427_nonnegative_value C *
      q132427_norm VE (q132427_sub VE x y).

Record q132427_continuous_linear_map
    {E F : Type}
    (VE : q132427_normed_real_vector_space E)
    (VF : q132427_normed_real_vector_space F)
    (L : E -> F) : Prop := {
  q132427_linear_add :
    forall x y : E,
      L (q132427_add VE x y) =
      q132427_add VF (L x) (L y);
  q132427_linear_smul :
    forall (a : R) (x : E),
      L (q132427_smul VE a x) =
      q132427_smul VF a (L x);
  q132427_linear_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : E,
        q132427_norm VF (L x) <=
        bound * q132427_norm VE x
}.

Definition q132427_has_frechet_derivative_within_at
    {E F : Type}
    (VE : q132427_normed_real_vector_space E)
    (VF : q132427_normed_real_vector_space F)
    (f : E -> F)
    (L : E -> F)
    (s : q132427_set E)
    (x : E) : Prop :=
  q132427_continuous_linear_map VE VF L /\
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : E,
        s y ->
        q132427_norm VE (q132427_sub VE y x) < delta ->
        q132427_norm VF
          (q132427_sub VF
            (q132427_sub VF (f y) (f x))
            (L (q132427_sub VE y x))) <=
        epsilon * q132427_norm VE (q132427_sub VE y x).

Definition q132427_differentiable_within_at
    {E F : Type}
    (VE : q132427_normed_real_vector_space E)
    (VF : q132427_normed_real_vector_space F)
    (f : E -> F)
    (s : q132427_set E)
    (x : E) : Prop :=
  exists L : E -> F,
    q132427_has_frechet_derivative_within_at
      VE VF f L s x.

Definition q132427_almost_everywhere_restrict
    {E : Type}
    {V : q132427_normed_real_vector_space E}
    (mu : q132427_borel_measure V)
    (s : q132427_set E)
    (P : E -> Prop) : Prop :=
  q132427_measure mu
    (q132427_intersection s (fun x => ~ P x)) =
  q132427_ennreal_zero.

Theorem LipschitzOnWith_ae_differentiableWithinAt :
  forall (E F : Type)
         (VE : q132427_normed_real_vector_space E)
         (VF : q132427_normed_real_vector_space F)
         (_ : q132427_finite_dimensional VE)
         (_ : q132427_finite_dimensional VF)
         (mu : q132427_borel_measure VE)
         (C : q132427_nonnegative_real)
         (f : E -> F)
         (s : q132427_set E),
    q132427_add_haar_measure mu ->
    q132427_borel_set VE s ->
    q132427_lipschitz_on_with VE VF C f s ->
    q132427_almost_everywhere_restrict mu s
      (fun x =>
        q132427_differentiable_within_at VE VF f s x).
Admitted.
