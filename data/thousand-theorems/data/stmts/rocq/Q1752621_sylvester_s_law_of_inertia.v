(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1752621
  (thousand-theorems__rocq__Q1752621), "Sylvester's law of inertia": every
  quadratic form on a finite-dimensional real vector space is isometrically
  equivalent to a sum of squares weighted by -1, 0, or 1. This file contains
  no proof.
*)

From Stdlib Require Import Vectors.Fin Reals.

Open Scope R_scope.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1752621_real_vector_space (V : Type) : Type := {
  q1752621_zero : V;
  q1752621_add : V -> V -> V;
  q1752621_neg : V -> V;
  q1752621_smul : R -> V -> V;
  q1752621_add_assoc :
    forall x y z : V,
      q1752621_add x (q1752621_add y z) =
      q1752621_add (q1752621_add x y) z;
  q1752621_add_comm :
    forall x y : V,
      q1752621_add x y = q1752621_add y x;
  q1752621_zero_add :
    forall x : V, q1752621_add q1752621_zero x = x;
  q1752621_add_zero :
    forall x : V, q1752621_add x q1752621_zero = x;
  q1752621_neg_add :
    forall x : V,
      q1752621_add (q1752621_neg x) x = q1752621_zero;
  q1752621_add_neg :
    forall x : V,
      q1752621_add x (q1752621_neg x) = q1752621_zero;
  q1752621_one_smul :
    forall x : V, q1752621_smul 1 x = x;
  q1752621_mul_smul :
    forall (a b : R) (x : V),
      q1752621_smul (a * b) x =
      q1752621_smul a (q1752621_smul b x);
  q1752621_add_smul :
    forall (a b : R) (x : V),
      q1752621_smul (a + b) x =
      q1752621_add
        (q1752621_smul a x) (q1752621_smul b x);
  q1752621_smul_add :
    forall (a : R) (x y : V),
      q1752621_smul a (q1752621_add x y) =
      q1752621_add
        (q1752621_smul a x) (q1752621_smul a y);
  q1752621_zero_smul :
    forall x : V, q1752621_smul 0 x = q1752621_zero;
  q1752621_smul_zero :
    forall a : R, q1752621_smul a q1752621_zero = q1752621_zero
}.

Arguments q1752621_zero {V} _.
Arguments q1752621_add {V} _ _ _.
Arguments q1752621_neg {V} _ _.
Arguments q1752621_smul {V} _ _ _.

Fixpoint q1752621_vector_sum
    {V : Type}
    (VS : q1752621_real_vector_space V)
    (n : nat) : (Fin.t n -> V) -> V :=
  match n as k return (Fin.t k -> V) -> V with
  | O => fun _ => q1752621_zero VS
  | S k =>
      fun terms =>
        q1752621_add VS
          (terms Fin.F1)
          (@q1752621_vector_sum V VS k
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1752621_vector_sum {V} VS n _.

Fixpoint q1752621_real_sum
    (n : nat) : (Fin.t n -> R) -> R :=
  match n as k return (Fin.t k -> R) -> R with
  | O => fun _ => 0
  | S k =>
      fun terms =>
        terms Fin.F1 +
        @q1752621_real_sum k (fun i => terms (Fin.FS i))
  end.

Record q1752621_finite_dimensional
    {V : Type}
    (VS : q1752621_real_vector_space V) : Type := {
  q1752621_dimension : nat;
  q1752621_basis : Fin.t q1752621_dimension -> V;
  q1752621_basis_spans :
    forall x : V,
      exists coefficients : Fin.t q1752621_dimension -> R,
        x =
        q1752621_vector_sum VS q1752621_dimension
          (fun i =>
            q1752621_smul VS
              (coefficients i) (q1752621_basis i));
  q1752621_basis_independent :
    forall coefficients : Fin.t q1752621_dimension -> R,
      q1752621_vector_sum VS q1752621_dimension
        (fun i =>
          q1752621_smul VS
            (coefficients i) (q1752621_basis i)) =
      q1752621_zero VS ->
      forall i : Fin.t q1752621_dimension,
        coefficients i = 0
}.

Arguments q1752621_dimension {V VS} _.

Record q1752621_bilinear_form
    {V : Type}
    (VS : q1752621_real_vector_space V) : Type := {
  q1752621_bilinear_apply : V -> V -> R;
  q1752621_bilinear_add_left :
    forall x y z : V,
      q1752621_bilinear_apply (q1752621_add VS x y) z =
      q1752621_bilinear_apply x z +
      q1752621_bilinear_apply y z;
  q1752621_bilinear_smul_left :
    forall (a : R) (x y : V),
      q1752621_bilinear_apply (q1752621_smul VS a x) y =
      a * q1752621_bilinear_apply x y;
  q1752621_bilinear_add_right :
    forall x y z : V,
      q1752621_bilinear_apply x (q1752621_add VS y z) =
      q1752621_bilinear_apply x y +
      q1752621_bilinear_apply x z;
  q1752621_bilinear_smul_right :
    forall (a : R) (x y : V),
      q1752621_bilinear_apply x (q1752621_smul VS a y) =
      a * q1752621_bilinear_apply x y
}.

Arguments q1752621_bilinear_apply {V VS} _ _ _.

Record q1752621_quadratic_form
    {V : Type}
    (VS : q1752621_real_vector_space V) : Type := {
  q1752621_quadratic_apply : V -> R;
  q1752621_quadratic_smul :
    forall (a : R) (x : V),
      q1752621_quadratic_apply (q1752621_smul VS a x) =
      (a * a) * q1752621_quadratic_apply x;
  q1752621_quadratic_has_companion :
    exists B : q1752621_bilinear_form VS,
      forall x y : V,
        q1752621_quadratic_apply (q1752621_add VS x y) =
        q1752621_quadratic_apply x +
        q1752621_quadratic_apply y +
        q1752621_bilinear_apply B x y
}.

Arguments q1752621_quadratic_apply {V VS} _ _.

Definition q1752621_quadratic_value
    {V : Type}
    {VS : q1752621_real_vector_space V}
    (Q : q1752621_quadratic_form VS)
    (x : V) : R :=
  q1752621_quadratic_apply Q x.

Record q1752621_linear_equiv_coordinates
    {V : Type}
    (VS : q1752621_real_vector_space V)
    (n : nat) : Type := {
  q1752621_to_coordinates : V -> Fin.t n -> R;
  q1752621_from_coordinates : (Fin.t n -> R) -> V;
  q1752621_from_to :
    forall x : V,
      q1752621_from_coordinates
        (q1752621_to_coordinates x) = x;
  q1752621_to_from :
    forall (coordinates : Fin.t n -> R) (i : Fin.t n),
      q1752621_to_coordinates
        (q1752621_from_coordinates coordinates) i =
      coordinates i;
  q1752621_to_add :
    forall (x y : V) (i : Fin.t n),
      q1752621_to_coordinates
        (q1752621_add VS x y) i =
      q1752621_to_coordinates x i +
      q1752621_to_coordinates y i;
  q1752621_to_smul :
    forall (a : R) (x : V) (i : Fin.t n),
      q1752621_to_coordinates
        (q1752621_smul VS a x) i =
      a * q1752621_to_coordinates x i
}.

Arguments q1752621_to_coordinates {V VS n} _ _ _.

Definition q1752621_weighted_sum_squares
    {n : nat}
    (weights coordinates : Fin.t n -> R) : R :=
  @q1752621_real_sum n
    (fun i => weights i * coordinates i * coordinates i).

Definition q1752621_equivalent_to_weighted_sum_squares
    {V : Type}
    {VS : q1752621_real_vector_space V}
    {n : nat}
    (Q : q1752621_quadratic_form VS)
    (weights : Fin.t n -> R) : Prop :=
  exists e : q1752621_linear_equiv_coordinates VS n,
    forall x : V,
      q1752621_quadratic_value Q x =
      q1752621_weighted_sum_squares
        weights (q1752621_to_coordinates e x).

Theorem QuadraticForm_equivalent_one_zero_neg_one_weighted_sum_squared :
  forall (V : Type)
         (VS : q1752621_real_vector_space V)
         (D : q1752621_finite_dimensional VS)
         (Q : q1752621_quadratic_form VS),
    exists weights : Fin.t (q1752621_dimension D) -> R,
      (forall i : Fin.t (q1752621_dimension D),
        weights i = (-1)%R \/
        weights i = 0%R \/
        weights i = 1%R) /\
      q1752621_equivalent_to_weighted_sum_squares Q weights.
Admitted.
