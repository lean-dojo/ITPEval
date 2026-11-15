(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527217
  (thousand-theorems__rocq__Q3527217), "M. Riesz extension theorem": a real
  linear functional on a subspace, nonnegative on its intersection with a
  pointed cone and satisfying the extension density condition, extends to a
  global linear functional nonnegative on the cone. This file contains no
  proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q3527217_real_vector_space (E : Type) : Type := {
  q3527217_zero : E;
  q3527217_add : E -> E -> E;
  q3527217_neg : E -> E;
  q3527217_smul : R -> E -> E;
  q3527217_add_assoc :
    forall x y z : E,
      q3527217_add x (q3527217_add y z) =
      q3527217_add (q3527217_add x y) z;
  q3527217_add_comm :
    forall x y : E,
      q3527217_add x y = q3527217_add y x;
  q3527217_zero_add :
    forall x : E,
      q3527217_add q3527217_zero x = x;
  q3527217_add_zero :
    forall x : E,
      q3527217_add x q3527217_zero = x;
  q3527217_neg_add :
    forall x : E,
      q3527217_add (q3527217_neg x) x = q3527217_zero;
  q3527217_add_neg :
    forall x : E,
      q3527217_add x (q3527217_neg x) = q3527217_zero;
  q3527217_one_smul :
    forall x : E,
      q3527217_smul 1 x = x;
  q3527217_mul_smul :
    forall (a b : R) (x : E),
      q3527217_smul (a * b) x =
      q3527217_smul a (q3527217_smul b x);
  q3527217_add_smul :
    forall (a b : R) (x : E),
      q3527217_smul (a + b) x =
      q3527217_add
        (q3527217_smul a x) (q3527217_smul b x);
  q3527217_smul_add :
    forall (a : R) (x y : E),
      q3527217_smul a (q3527217_add x y) =
      q3527217_add
        (q3527217_smul a x) (q3527217_smul a y);
  q3527217_zero_smul :
    forall x : E,
      q3527217_smul 0 x = q3527217_zero;
  q3527217_smul_zero :
    forall a : R,
      q3527217_smul a q3527217_zero = q3527217_zero
}.

Arguments q3527217_zero {E} _.
Arguments q3527217_add {E} _ _ _.
Arguments q3527217_neg {E} _ _.
Arguments q3527217_smul {E} _ _ _.

Record q3527217_subspace
    {E : Type}
    (V : q3527217_real_vector_space E) : Type := {
  q3527217_subspace_pred : E -> Prop;
  q3527217_subspace_zero :
    q3527217_subspace_pred (q3527217_zero V);
  q3527217_subspace_add :
    forall x y : E,
      q3527217_subspace_pred x ->
      q3527217_subspace_pred y ->
      q3527217_subspace_pred (q3527217_add V x y);
  q3527217_subspace_smul :
    forall (a : R) (x : E),
      q3527217_subspace_pred x ->
      q3527217_subspace_pred (q3527217_smul V a x)
}.

Arguments q3527217_subspace_pred {E V} _ _.

Definition q3527217_subspace_carrier
    {E : Type}
    {V : q3527217_real_vector_space E}
    (P : q3527217_subspace V) : Type :=
  {x : E | q3527217_subspace_pred P x}.

Definition q3527217_subspace_add_value
    {E : Type}
    {V : q3527217_real_vector_space E}
    {P : q3527217_subspace V}
    (x y : q3527217_subspace_carrier P) :
    q3527217_subspace_carrier P :=
  exist _ (q3527217_add V (proj1_sig x) (proj1_sig y))
    (q3527217_subspace_add P
      (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y)).

Definition q3527217_subspace_smul_value
    {E : Type}
    {V : q3527217_real_vector_space E}
    {P : q3527217_subspace V}
    (a : R) (x : q3527217_subspace_carrier P) :
    q3527217_subspace_carrier P :=
  exist _ (q3527217_smul V a (proj1_sig x))
    (q3527217_subspace_smul P a (proj1_sig x) (proj2_sig x)).

Record q3527217_pointed_cone
    {E : Type}
    (V : q3527217_real_vector_space E) : Type := {
  q3527217_cone_pred : E -> Prop;
  q3527217_cone_zero :
    q3527217_cone_pred (q3527217_zero V);
  q3527217_cone_add :
    forall x y : E,
      q3527217_cone_pred x ->
      q3527217_cone_pred y ->
      q3527217_cone_pred (q3527217_add V x y);
  q3527217_cone_smul_nonnegative :
    forall (a : R) (x : E),
      0 <= a ->
      q3527217_cone_pred x ->
      q3527217_cone_pred (q3527217_smul V a x)
}.

Arguments q3527217_cone_pred {E V} _ _.

Record q3527217_partial_linear_functional
    {E : Type}
    {V : q3527217_real_vector_space E}
    (P : q3527217_subspace V) : Type := {
  q3527217_partial_apply : q3527217_subspace_carrier P -> R;
  q3527217_partial_apply_membership_irrelevant :
    forall (x : E)
           (hx hy : q3527217_subspace_pred P x),
      q3527217_partial_apply (exist _ x hx) =
      q3527217_partial_apply (exist _ x hy);
  q3527217_partial_map_add :
    forall x y : q3527217_subspace_carrier P,
      q3527217_partial_apply
        (q3527217_subspace_add_value x y) =
      q3527217_partial_apply x + q3527217_partial_apply y;
  q3527217_partial_map_smul :
    forall (a : R) (x : q3527217_subspace_carrier P),
      q3527217_partial_apply
        (q3527217_subspace_smul_value a x) =
      a * q3527217_partial_apply x
}.

Arguments q3527217_partial_apply {E V P} _ _.

Record q3527217_linear_functional
    {E : Type}
    (V : q3527217_real_vector_space E) : Type := {
  q3527217_linear_apply : E -> R;
  q3527217_linear_map_add :
    forall x y : E,
      q3527217_linear_apply (q3527217_add V x y) =
      q3527217_linear_apply x + q3527217_linear_apply y;
  q3527217_linear_map_smul :
    forall (a : R) (x : E),
      q3527217_linear_apply (q3527217_smul V a x) =
      a * q3527217_linear_apply x
}.

Arguments q3527217_linear_apply {E V} _ _.

Theorem riesz_extension :
  forall (E : Type)
         (V : q3527217_real_vector_space E)
         (s : q3527217_pointed_cone V)
         (P : q3527217_subspace V)
         (f : q3527217_partial_linear_functional P),
    (forall x : q3527217_subspace_carrier P,
      q3527217_cone_pred s (proj1_sig x) ->
      0 <= q3527217_partial_apply f x) ->
    (forall y : E,
      exists x : q3527217_subspace_carrier P,
        q3527217_cone_pred s
          (q3527217_add V (proj1_sig x) y)) ->
    exists g : q3527217_linear_functional V,
      (forall x : q3527217_subspace_carrier P,
        q3527217_linear_apply g (proj1_sig x) =
        q3527217_partial_apply f x) /\
      forall x : E,
        q3527217_cone_pred s x ->
        0 <= q3527217_linear_apply g x.
Admitted.
