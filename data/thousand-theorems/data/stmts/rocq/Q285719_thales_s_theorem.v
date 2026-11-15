(*
  Statement-only formalization of Thousand Theorems corpus artifact Q285719
  (thousand-theorems__rocq__Q285719), "Thales's theorem": in an arbitrary
  real inner-product affine space, if two points are endpoints of a diameter
  of a sphere, the angle they subtend at a third point is pi/2 exactly when
  that third point lies on the sphere. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q285719_real_inner_product_space (V : Type) : Type := {
  q285719_zero : V;
  q285719_add : V -> V -> V;
  q285719_neg : V -> V;
  q285719_smul : R -> V -> V;
  q285719_inner : V -> V -> R;

  q285719_add_assoc :
    forall x y z : V,
      q285719_add x (q285719_add y z) =
      q285719_add (q285719_add x y) z;
  q285719_add_comm :
    forall x y : V, q285719_add x y = q285719_add y x;
  q285719_add_zero :
    forall x : V, q285719_add x q285719_zero = x;
  q285719_add_neg :
    forall x : V, q285719_add x (q285719_neg x) = q285719_zero;

  q285719_one_smul :
    forall x : V, q285719_smul 1 x = x;
  q285719_mul_smul :
    forall (a b : R) (x : V),
      q285719_smul (a * b) x =
      q285719_smul a (q285719_smul b x);
  q285719_smul_add :
    forall (a : R) (x y : V),
      q285719_smul a (q285719_add x y) =
      q285719_add (q285719_smul a x) (q285719_smul a y);
  q285719_add_smul :
    forall (a b : R) (x : V),
      q285719_smul (a + b) x =
      q285719_add (q285719_smul a x) (q285719_smul b x);

  q285719_inner_add_left :
    forall x y z : V,
      q285719_inner (q285719_add x y) z =
      q285719_inner x z + q285719_inner y z;
  q285719_inner_smul_left :
    forall (a : R) (x y : V),
      q285719_inner (q285719_smul a x) y =
      a * q285719_inner x y;
  q285719_inner_symm :
    forall x y : V, q285719_inner x y = q285719_inner y x;
  q285719_inner_nonnegative :
    forall x : V, 0 <= q285719_inner x x;
  q285719_inner_eq_zero :
    forall x : V,
      q285719_inner x x = 0 <-> x = q285719_zero
}.

Arguments q285719_zero {V} _.
Arguments q285719_add {V} _ _ _.
Arguments q285719_neg {V} _ _.
Arguments q285719_smul {V} _ _ _.
Arguments q285719_inner {V} _ _ _.

Record q285719_affine_torsor
    (V P : Type) (E : q285719_real_inner_product_space V) : Type := {
  q285719_vadd : V -> P -> P;
  q285719_vsub : P -> P -> V;
  q285719_zero_vadd :
    forall p : P, q285719_vadd (q285719_zero E) p = p;
  q285719_add_vadd :
    forall (x y : V) (p : P),
      q285719_vadd (q285719_add E x y) p =
      q285719_vadd x (q285719_vadd y p);
  q285719_vsub_vadd :
    forall (x : V) (p : P),
      q285719_vsub (q285719_vadd x p) p = x;
  q285719_vadd_vsub :
    forall p q : P,
      q285719_vadd (q285719_vsub p q) q = p
}.

Arguments q285719_vadd {V P E} _ _ _.
Arguments q285719_vsub {V P E} _ _ _.

Definition q285719_norm
    {V : Type}
    (E : q285719_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q285719_inner E x x).

Definition q285719_dist
    {V P : Type}
    {E : q285719_real_inner_product_space V}
    (A : @q285719_affine_torsor V P E)
    (p q : P) : R :=
  q285719_norm E (q285719_vsub A p q).

Definition q285719_midpoint
    {V P : Type}
    {E : q285719_real_inner_product_space V}
    (A : @q285719_affine_torsor V P E)
    (p q : P) : P :=
  q285719_vadd A
    (q285719_smul E (1 / 2) (q285719_vsub A p q)) q.

Record q285719_sphere (P : Type) : Type := {
  q285719_center : P;
  q285719_radius : R
}.

Arguments q285719_center {P} _.
Arguments q285719_radius {P} _.

Definition q285719_mem_sphere
    {V P : Type}
    {E : q285719_real_inner_product_space V}
    (A : @q285719_affine_torsor V P E)
    (s : q285719_sphere P)
    (p : P) : Prop :=
  q285719_dist A p (q285719_center s) = q285719_radius s.

Definition q285719_is_diameter
    {V P : Type}
    {E : q285719_real_inner_product_space V}
    (A : @q285719_affine_torsor V P E)
    (s : q285719_sphere P)
    (p1 p3 : P) : Prop :=
  q285719_mem_sphere A s p1 /\
  q285719_midpoint A p1 p3 = q285719_center s.

Definition q285719_angle_eq_pi_div_two
    {V P : Type}
    {E : q285719_real_inner_product_space V}
    (A : @q285719_affine_torsor V P E)
    (p1 p2 p3 : P) : Prop :=
  q285719_inner E
    (q285719_vsub A p1 p2)
    (q285719_vsub A p3 p2) = 0.

Theorem EuclideanGeometry_Sphere_thales_theorem :
  forall (V P : Type)
         (E : q285719_real_inner_product_space V)
         (A : @q285719_affine_torsor V P E)
         (p1 p2 p3 : P)
         (s : q285719_sphere P),
    q285719_is_diameter A s p1 p3 ->
    (q285719_angle_eq_pi_div_two A p1 p2 p3 <->
     q285719_mem_sphere A s p2).
Admitted.
