(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2267175
  (thousand-theorems__rocq__Q2267175), "Tangent-secant theorem": in an
  arbitrary real inner-product affine space, the squared distance from a
  point to a tangent point of a sphere equals the product of its
  distances to two points where a secant through it meets the sphere.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q2267175_real_inner_product_space (V : Type) : Type := {
  q2267175_zero : V;
  q2267175_add : V -> V -> V;
  q2267175_neg : V -> V;
  q2267175_smul : R -> V -> V;
  q2267175_inner : V -> V -> R;

  q2267175_add_assoc :
    forall x y z : V,
      q2267175_add x (q2267175_add y z) =
      q2267175_add (q2267175_add x y) z;
  q2267175_add_comm :
    forall x y : V, q2267175_add x y = q2267175_add y x;
  q2267175_add_zero :
    forall x : V, q2267175_add x q2267175_zero = x;
  q2267175_add_neg :
    forall x : V, q2267175_add x (q2267175_neg x) = q2267175_zero;

  q2267175_one_smul :
    forall x : V, q2267175_smul 1 x = x;
  q2267175_mul_smul :
    forall (a b : R) (x : V),
      q2267175_smul (a * b) x =
      q2267175_smul a (q2267175_smul b x);
  q2267175_smul_add :
    forall (a : R) (x y : V),
      q2267175_smul a (q2267175_add x y) =
      q2267175_add (q2267175_smul a x) (q2267175_smul a y);
  q2267175_add_smul :
    forall (a b : R) (x : V),
      q2267175_smul (a + b) x =
      q2267175_add (q2267175_smul a x) (q2267175_smul b x);

  q2267175_inner_add_left :
    forall x y z : V,
      q2267175_inner (q2267175_add x y) z =
      q2267175_inner x z + q2267175_inner y z;
  q2267175_inner_smul_left :
    forall (a : R) (x y : V),
      q2267175_inner (q2267175_smul a x) y =
      a * q2267175_inner x y;
  q2267175_inner_symm :
    forall x y : V, q2267175_inner x y = q2267175_inner y x;
  q2267175_inner_nonnegative :
    forall x : V, 0 <= q2267175_inner x x;
  q2267175_inner_eq_zero :
    forall x : V,
      q2267175_inner x x = 0 <-> x = q2267175_zero
}.

Arguments q2267175_zero {V} _.
Arguments q2267175_add {V} _ _ _.
Arguments q2267175_neg {V} _ _.
Arguments q2267175_smul {V} _ _ _.
Arguments q2267175_inner {V} _ _ _.

Record q2267175_affine_torsor
    (V P : Type) (E : q2267175_real_inner_product_space V) : Type := {
  q2267175_vadd : V -> P -> P;
  q2267175_vsub : P -> P -> V;
  q2267175_zero_vadd :
    forall p : P, q2267175_vadd (q2267175_zero E) p = p;
  q2267175_add_vadd :
    forall (x y : V) (p : P),
      q2267175_vadd (q2267175_add E x y) p =
      q2267175_vadd x (q2267175_vadd y p);
  q2267175_vsub_vadd :
    forall (x : V) (p : P),
      q2267175_vsub (q2267175_vadd x p) p = x;
  q2267175_vadd_vsub :
    forall p q : P,
      q2267175_vadd (q2267175_vsub p q) q = p
}.

Arguments q2267175_vadd {V P E} _ _ _.
Arguments q2267175_vsub {V P E} _ _ _.

Definition q2267175_norm
    {V : Type}
    (E : q2267175_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q2267175_inner E x x).

Definition q2267175_dist
    {V P : Type}
    {E : q2267175_real_inner_product_space V}
    (A : @q2267175_affine_torsor V P E)
    (p q : P) : R :=
  q2267175_norm E (q2267175_vsub A p q).

Record q2267175_sphere (P : Type) : Type := {
  q2267175_center : P;
  q2267175_radius : R
}.

Arguments q2267175_center {P} _.
Arguments q2267175_radius {P} _.

Definition q2267175_mem_sphere
    {V P : Type}
    {E : q2267175_real_inner_product_space V}
    (A : @q2267175_affine_torsor V P E)
    (s : q2267175_sphere P)
    (x : P) : Prop :=
  q2267175_dist A x (q2267175_center s) = q2267175_radius s.

Definition q2267175_mem_line
    {V P : Type}
    {E : q2267175_real_inner_product_space V}
    (A : @q2267175_affine_torsor V P E)
    (a b p : P) : Prop :=
  exists lambda : R,
    p =
      q2267175_vadd A
        (q2267175_smul E lambda (q2267175_vsub A b a)) a.

Definition q2267175_is_tangent_at
    {V P : Type}
    {E : q2267175_real_inner_product_space V}
    (A : @q2267175_affine_torsor V P E)
    (s : q2267175_sphere P)
    (t p : P) : Prop :=
  q2267175_mem_sphere A s t /\
  q2267175_inner E
    (q2267175_vsub A p t)
    (q2267175_vsub A t (q2267175_center s)) = 0.

Theorem EuclideanGeometry_Sphere_dist_sq_eq_mul_dist_of_tangent_and_secant :
  forall (V P : Type)
         (E : q2267175_real_inner_product_space V)
         (A : @q2267175_affine_torsor V P E)
         (a b t p : P)
         (s : q2267175_sphere P),
    q2267175_mem_sphere A s a ->
    q2267175_mem_sphere A s b ->
    q2267175_mem_line A a b p ->
    q2267175_is_tangent_at A s t p ->
    q2267175_dist A p t ^ 2 =
      q2267175_dist A p a * q2267175_dist A p b.
Admitted.
