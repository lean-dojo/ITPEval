(*
  Statement-only formalization of Thousand Theorems corpus artifact Q5421989
  (thousand-theorems__rocq__Q5421989), "Exterior angle theorem": in an
  arbitrary real inner-product affine space, if one point lies strictly
  between an exterior point and a triangle vertex, the exterior angle equals
  the sum of the two remote interior angles. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q5421989_real_inner_product_space (V : Type) : Type := {
  q5421989_zero : V;
  q5421989_add : V -> V -> V;
  q5421989_neg : V -> V;
  q5421989_smul : R -> V -> V;
  q5421989_inner : V -> V -> R;

  q5421989_add_assoc :
    forall x y z : V,
      q5421989_add x (q5421989_add y z) =
      q5421989_add (q5421989_add x y) z;
  q5421989_add_comm :
    forall x y : V, q5421989_add x y = q5421989_add y x;
  q5421989_add_zero :
    forall x : V, q5421989_add x q5421989_zero = x;
  q5421989_add_neg :
    forall x : V, q5421989_add x (q5421989_neg x) = q5421989_zero;

  q5421989_one_smul :
    forall x : V, q5421989_smul 1 x = x;
  q5421989_mul_smul :
    forall (a b : R) (x : V),
      q5421989_smul (a * b) x =
      q5421989_smul a (q5421989_smul b x);
  q5421989_smul_add :
    forall (a : R) (x y : V),
      q5421989_smul a (q5421989_add x y) =
      q5421989_add (q5421989_smul a x) (q5421989_smul a y);
  q5421989_add_smul :
    forall (a b : R) (x : V),
      q5421989_smul (a + b) x =
      q5421989_add (q5421989_smul a x) (q5421989_smul b x);

  q5421989_inner_add_left :
    forall x y z : V,
      q5421989_inner (q5421989_add x y) z =
      q5421989_inner x z + q5421989_inner y z;
  q5421989_inner_smul_left :
    forall (a : R) (x y : V),
      q5421989_inner (q5421989_smul a x) y =
      a * q5421989_inner x y;
  q5421989_inner_symm :
    forall x y : V, q5421989_inner x y = q5421989_inner y x;
  q5421989_inner_nonnegative :
    forall x : V, 0 <= q5421989_inner x x;
  q5421989_inner_eq_zero :
    forall x : V,
      q5421989_inner x x = 0 <-> x = q5421989_zero
}.

Arguments q5421989_zero {V} _.
Arguments q5421989_add {V} _ _ _.
Arguments q5421989_neg {V} _ _.
Arguments q5421989_smul {V} _ _ _.
Arguments q5421989_inner {V} _ _ _.

Record q5421989_affine_torsor
    (V P : Type) (E : q5421989_real_inner_product_space V) : Type := {
  q5421989_vadd : V -> P -> P;
  q5421989_vsub : P -> P -> V;
  q5421989_zero_vadd :
    forall p : P, q5421989_vadd (q5421989_zero E) p = p;
  q5421989_add_vadd :
    forall (x y : V) (p : P),
      q5421989_vadd (q5421989_add E x y) p =
      q5421989_vadd x (q5421989_vadd y p);
  q5421989_vsub_vadd :
    forall (x : V) (p : P),
      q5421989_vsub (q5421989_vadd x p) p = x;
  q5421989_vadd_vsub :
    forall p q : P,
      q5421989_vadd (q5421989_vsub p q) q = p
}.

Arguments q5421989_vadd {V P E} _ _ _.
Arguments q5421989_vsub {V P E} _ _ _.

Definition q5421989_norm
    {V : Type}
    (E : q5421989_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q5421989_inner E x x).

Definition q5421989_angle
    {V P : Type}
    {E : q5421989_real_inner_product_space V}
    (A : @q5421989_affine_torsor V P E)
    (p1 p2 p3 : P) : R :=
  let x := q5421989_vsub A p1 p2 in
  let y := q5421989_vsub A p3 p2 in
  acos
    (q5421989_inner E x y /
      (q5421989_norm E x * q5421989_norm E y)).

Definition q5421989_strictly_between
    {V P : Type}
    {E : q5421989_real_inner_product_space V}
    (A : @q5421989_affine_torsor V P E)
    (p p1 p2 : P) : Prop :=
  (exists t : R,
    0 <= t /\
    t <= 1 /\
    p1 =
      q5421989_vadd A
        (q5421989_smul E t (q5421989_vsub A p2 p)) p) /\
  p1 <> p /\
  p1 <> p2.

Theorem EuclideanGeometry_exterior_angle_eq_angle_add_angle :
  forall (V P : Type)
         (E : q5421989_real_inner_product_space V)
         (A : @q5421989_affine_torsor V P E)
         (p1 p2 p3 p : P),
    q5421989_strictly_between A p p1 p2 ->
    q5421989_angle A p3 p1 p =
      q5421989_angle A p1 p3 p2 +
      q5421989_angle A p3 p2 p1.
Admitted.
