(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1144897
  (thousand-theorems__rocq__Q1144897), "Brouwer fixed-point theorem": every
  continuous self-map of a nonempty compact convex subset of a
  finite-dimensional real normed vector space has a fixed point. This file
  contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals List.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q1144897_set (A : Type) : Type := A -> Prop.

Record q1144897_normed_real_vector_space (V : Type) : Type := {
  q1144897_zero : V;
  q1144897_add : V -> V -> V;
  q1144897_neg : V -> V;
  q1144897_smul : R -> V -> V;
  q1144897_norm : V -> R;
  q1144897_add_assoc :
    forall x y z : V,
      q1144897_add x (q1144897_add y z) =
      q1144897_add (q1144897_add x y) z;
  q1144897_add_comm :
    forall x y : V,
      q1144897_add x y = q1144897_add y x;
  q1144897_zero_add :
    forall x : V, q1144897_add q1144897_zero x = x;
  q1144897_add_zero :
    forall x : V, q1144897_add x q1144897_zero = x;
  q1144897_neg_add :
    forall x : V,
      q1144897_add (q1144897_neg x) x = q1144897_zero;
  q1144897_add_neg :
    forall x : V,
      q1144897_add x (q1144897_neg x) = q1144897_zero;
  q1144897_one_smul :
    forall x : V, q1144897_smul 1 x = x;
  q1144897_mul_smul :
    forall (a b : R) (x : V),
      q1144897_smul (a * b) x =
      q1144897_smul a (q1144897_smul b x);
  q1144897_add_smul :
    forall (a b : R) (x : V),
      q1144897_smul (a + b) x =
      q1144897_add
        (q1144897_smul a x) (q1144897_smul b x);
  q1144897_smul_add :
    forall (a : R) (x y : V),
      q1144897_smul a (q1144897_add x y) =
      q1144897_add
        (q1144897_smul a x) (q1144897_smul a y);
  q1144897_zero_smul :
    forall x : V, q1144897_smul 0 x = q1144897_zero;
  q1144897_smul_zero :
    forall a : R, q1144897_smul a q1144897_zero = q1144897_zero;
  q1144897_norm_nonnegative :
    forall x : V, 0 <= q1144897_norm x;
  q1144897_norm_eq_zero :
    forall x : V,
      q1144897_norm x = 0 <-> x = q1144897_zero;
  q1144897_norm_add_le :
    forall x y : V,
      q1144897_norm (q1144897_add x y) <=
      q1144897_norm x + q1144897_norm y;
  q1144897_norm_smul :
    forall (a : R) (x : V),
      q1144897_norm (q1144897_smul a x) =
      Rabs a * q1144897_norm x
}.

Arguments q1144897_zero {V} _.
Arguments q1144897_add {V} _ _ _.
Arguments q1144897_neg {V} _ _.
Arguments q1144897_smul {V} _ _ _.
Arguments q1144897_norm {V} _ _.

Definition q1144897_sub {V : Type}
    (N : q1144897_normed_real_vector_space V)
    (x y : V) : V :=
  q1144897_add N x (q1144897_neg N y).

Fixpoint q1144897_vector_sum
    {V : Type}
    (N : q1144897_normed_real_vector_space V)
    (n : nat) : (Fin.t n -> V) -> V :=
  match n as k return (Fin.t k -> V) -> V with
  | O => fun _ => q1144897_zero N
  | S k =>
      fun terms =>
        q1144897_add N
          (terms Fin.F1)
          (@q1144897_vector_sum V N k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1144897_vector_sum {V} N n _.

Definition q1144897_finite_dimensional
    {V : Type}
    (N : q1144897_normed_real_vector_space V) : Prop :=
  exists (n : nat) (basis : Fin.t n -> V),
    (forall x : V,
      exists coefficients : Fin.t n -> R,
        x =
        q1144897_vector_sum N n
          (fun i =>
            q1144897_smul N
              (coefficients i) (basis i))) /\
    (forall coefficients : Fin.t n -> R,
      q1144897_vector_sum N n
        (fun i =>
          q1144897_smul N
            (coefficients i) (basis i)) =
      q1144897_zero N ->
      forall i : Fin.t n, coefficients i = 0).

Definition q1144897_convex
    {V : Type}
    (N : q1144897_normed_real_vector_space V)
    (S : q1144897_set V) : Prop :=
  forall (x y : V) (t : R),
    S x ->
    S y ->
    0 <= t ->
    t <= 1 ->
    S
      (q1144897_add N
        (q1144897_smul N t x)
        (q1144897_smul N (1 - t) y)).

Definition q1144897_norm_open
    {V : Type}
    (N : q1144897_normed_real_vector_space V)
    (U : q1144897_set V) : Prop :=
  forall x : V,
    U x ->
    exists epsilon : R,
      0 < epsilon /\
      forall y : V,
        q1144897_norm N (q1144897_sub N y x) < epsilon ->
        U y.

Definition q1144897_compact
    {V : Type}
    (N : q1144897_normed_real_vector_space V)
    (S : q1144897_set V) : Prop :=
  forall (J : Type) (U : J -> q1144897_set V),
    (forall j : J, q1144897_norm_open N (U j)) ->
    (forall x : V, S x -> exists j : J, U j x) ->
    exists finite_subcover : list J,
      forall x : V,
        S x ->
        exists j : J, In j finite_subcover /\ U j x.

Record q1144897_member
    {V : Type}
    (S : q1144897_set V) : Type := {
  q1144897_value : V;
  q1144897_value_mem : S q1144897_value
}.

Arguments q1144897_value {V S} _.

Definition q1144897_continuous_self_map
    {V : Type}
    (N : q1144897_normed_real_vector_space V)
    (S : q1144897_set V)
    (f : q1144897_member S -> q1144897_member S) : Prop :=
  forall (x : q1144897_member S) (epsilon : R),
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : q1144897_member S,
        q1144897_norm N
          (q1144897_sub N
            (q1144897_value y) (q1144897_value x)) < delta ->
        q1144897_norm N
          (q1144897_sub N
            (q1144897_value (f y))
            (q1144897_value (f x))) < epsilon.

Arguments q1144897_continuous_self_map {V} N S f.

Theorem brouwer_fixed_point :
  forall (V : Type)
         (N : q1144897_normed_real_vector_space V),
    q1144897_finite_dimensional N ->
    forall S : q1144897_set V,
      q1144897_convex N S ->
      q1144897_compact N S ->
      (exists x : V, S x) ->
      forall f : q1144897_member S -> q1144897_member S,
        q1144897_continuous_self_map N S f ->
        exists x : q1144897_member S, f x = x.
Proof.
Admitted.
