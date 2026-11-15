(*
  Statement-only formalization of Thousand Theorems corpus artifact Q11518
  (thousand-theorems__rocq__Q11518), "Pythagorean theorem": in an arbitrary
  real inner-product affine space, the squared-distance identity holds exactly
  when the angle at the middle point is pi/2. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q11518_real_inner_product_space (V : Type) : Type := {
  q11518_zero : V;
  q11518_add : V -> V -> V;
  q11518_neg : V -> V;
  q11518_smul : R -> V -> V;
  q11518_inner : V -> V -> R;

  q11518_add_assoc :
    forall x y z : V,
      q11518_add x (q11518_add y z) =
      q11518_add (q11518_add x y) z;
  q11518_add_comm :
    forall x y : V, q11518_add x y = q11518_add y x;
  q11518_add_zero :
    forall x : V, q11518_add x q11518_zero = x;
  q11518_add_neg :
    forall x : V, q11518_add x (q11518_neg x) = q11518_zero;

  q11518_one_smul :
    forall x : V, q11518_smul 1 x = x;
  q11518_mul_smul :
    forall (a b : R) (x : V),
      q11518_smul (a * b) x = q11518_smul a (q11518_smul b x);
  q11518_smul_add :
    forall (a : R) (x y : V),
      q11518_smul a (q11518_add x y) =
      q11518_add (q11518_smul a x) (q11518_smul a y);
  q11518_add_smul :
    forall (a b : R) (x : V),
      q11518_smul (a + b) x =
      q11518_add (q11518_smul a x) (q11518_smul b x);

  q11518_inner_add_left :
    forall x y z : V,
      q11518_inner (q11518_add x y) z =
      q11518_inner x z + q11518_inner y z;
  q11518_inner_smul_left :
    forall (a : R) (x y : V),
      q11518_inner (q11518_smul a x) y =
      a * q11518_inner x y;
  q11518_inner_symm :
    forall x y : V, q11518_inner x y = q11518_inner y x;
  q11518_inner_nonnegative :
    forall x : V, 0 <= q11518_inner x x;
  q11518_inner_eq_zero :
    forall x : V, q11518_inner x x = 0 <-> x = q11518_zero
}.

Arguments q11518_zero {V} _.
Arguments q11518_add {V} _ _ _.
Arguments q11518_neg {V} _ _.
Arguments q11518_smul {V} _ _ _.
Arguments q11518_inner {V} _ _ _.

Record q11518_affine_torsor
    (V P : Type) (E : q11518_real_inner_product_space V) : Type := {
  q11518_vadd : V -> P -> P;
  q11518_vsub : P -> P -> V;
  q11518_zero_vadd :
    forall p : P, q11518_vadd (q11518_zero E) p = p;
  q11518_add_vadd :
    forall (x y : V) (p : P),
      q11518_vadd (q11518_add E x y) p =
      q11518_vadd x (q11518_vadd y p);
  q11518_vsub_vadd :
    forall (x : V) (p : P),
      q11518_vsub (q11518_vadd x p) p = x;
  q11518_vadd_vsub :
    forall p q : P,
      q11518_vadd (q11518_vsub p q) q = p
}.

Arguments q11518_vadd {V P E} _ _ _.
Arguments q11518_vsub {V P E} _ _ _.

Definition q11518_norm
    {V : Type} (E : q11518_real_inner_product_space V) (x : V) : R :=
  sqrt (q11518_inner E x x).

Definition q11518_dist
    {V P : Type}
    {E : q11518_real_inner_product_space V}
    (A : @q11518_affine_torsor V P E)
    (p q : P) : R :=
  q11518_norm E (q11518_vsub A p q).

Definition q11518_angle
    {V P : Type}
    {E : q11518_real_inner_product_space V}
    (A : @q11518_affine_torsor V P E)
    (p1 p2 p3 : P) : R :=
  let x := q11518_vsub A p1 p2 in
  let y := q11518_vsub A p3 p2 in
  acos
    (q11518_inner E x y /
      (q11518_norm E x * q11518_norm E y)).

Theorem EuclideanGeometry_dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two :
  forall (V P : Type)
         (E : q11518_real_inner_product_space V)
         (A : @q11518_affine_torsor V P E)
         (p1 p2 p3 : P),
    q11518_dist A p1 p3 * q11518_dist A p1 p3 =
      q11518_dist A p1 p2 * q11518_dist A p1 p2 +
      q11518_dist A p3 p2 * q11518_dist A p3 p2 <->
    q11518_angle A p1 p2 p3 = PI / 2.
Admitted.
