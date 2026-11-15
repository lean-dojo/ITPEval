(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2226868
  (thousand-theorems__rocq__Q2226868), "Geometric mean theorem": in an
  arbitrary real inner-product affine space, the square of a right triangle's
  altitude to the hypotenuse equals the product of the two hypotenuse segments.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q2226868_real_inner_product_space (V : Type) : Type := {
  q2226868_zero : V;
  q2226868_add : V -> V -> V;
  q2226868_neg : V -> V;
  q2226868_smul : R -> V -> V;
  q2226868_inner : V -> V -> R;

  q2226868_add_assoc :
    forall x y z : V,
      q2226868_add x (q2226868_add y z) =
      q2226868_add (q2226868_add x y) z;
  q2226868_add_comm :
    forall x y : V, q2226868_add x y = q2226868_add y x;
  q2226868_add_zero :
    forall x : V, q2226868_add x q2226868_zero = x;
  q2226868_add_neg :
    forall x : V, q2226868_add x (q2226868_neg x) = q2226868_zero;

  q2226868_one_smul :
    forall x : V, q2226868_smul 1 x = x;
  q2226868_mul_smul :
    forall (a b : R) (x : V),
      q2226868_smul (a * b) x =
      q2226868_smul a (q2226868_smul b x);
  q2226868_smul_add :
    forall (a : R) (x y : V),
      q2226868_smul a (q2226868_add x y) =
      q2226868_add (q2226868_smul a x) (q2226868_smul a y);
  q2226868_add_smul :
    forall (a b : R) (x : V),
      q2226868_smul (a + b) x =
      q2226868_add (q2226868_smul a x) (q2226868_smul b x);

  q2226868_inner_add_left :
    forall x y z : V,
      q2226868_inner (q2226868_add x y) z =
      q2226868_inner x z + q2226868_inner y z;
  q2226868_inner_smul_left :
    forall (a : R) (x y : V),
      q2226868_inner (q2226868_smul a x) y =
      a * q2226868_inner x y;
  q2226868_inner_symm :
    forall x y : V, q2226868_inner x y = q2226868_inner y x;
  q2226868_inner_nonnegative :
    forall x : V, 0 <= q2226868_inner x x;
  q2226868_inner_eq_zero :
    forall x : V,
      q2226868_inner x x = 0 <-> x = q2226868_zero
}.

Arguments q2226868_zero {V} _.
Arguments q2226868_add {V} _ _ _.
Arguments q2226868_neg {V} _ _.
Arguments q2226868_smul {V} _ _ _.
Arguments q2226868_inner {V} _ _ _.

Record q2226868_affine_torsor
    (V P : Type) (E : q2226868_real_inner_product_space V) : Type := {
  q2226868_vadd : V -> P -> P;
  q2226868_vsub : P -> P -> V;
  q2226868_zero_vadd :
    forall p : P, q2226868_vadd (q2226868_zero E) p = p;
  q2226868_add_vadd :
    forall (x y : V) (p : P),
      q2226868_vadd (q2226868_add E x y) p =
      q2226868_vadd x (q2226868_vadd y p);
  q2226868_vsub_vadd :
    forall (x : V) (p : P),
      q2226868_vsub (q2226868_vadd x p) p = x;
  q2226868_vadd_vsub :
    forall p q : P,
      q2226868_vadd (q2226868_vsub p q) q = p
}.

Arguments q2226868_vadd {V P E} _ _ _.
Arguments q2226868_vsub {V P E} _ _ _.

Definition q2226868_norm
    {V : Type}
    (E : q2226868_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q2226868_inner E x x).

Definition q2226868_dist
    {V P : Type}
    {E : q2226868_real_inner_product_space V}
    (A : @q2226868_affine_torsor V P E)
    (p q : P) : R :=
  q2226868_norm E (q2226868_vsub A p q).

Definition q2226868_angle
    {V P : Type}
    {E : q2226868_real_inner_product_space V}
    (A : @q2226868_affine_torsor V P E)
    (p1 p2 p3 : P) : R :=
  let x := q2226868_vsub A p1 p2 in
  let y := q2226868_vsub A p3 p2 in
  acos
    (q2226868_inner E x y /
      (q2226868_norm E x * q2226868_norm E y)).

Definition q2226868_strictly_between
    {V P : Type}
    {E : q2226868_real_inner_product_space V}
    (A : @q2226868_affine_torsor V P E)
    (p1 p4 p3 : P) : Prop :=
  (exists t : R,
    0 <= t /\
    t <= 1 /\
    p4 =
      q2226868_vadd A
        (q2226868_smul E t (q2226868_vsub A p3 p1)) p1) /\
  p4 <> p1 /\
  p4 <> p3.

Theorem EuclideanGeometry_dist_sq_eq_dist_mul_dist_of_angle_eq_pi_div_two :
  forall (V P : Type)
         (E : q2226868_real_inner_product_space V)
         (A : @q2226868_affine_torsor V P E)
         (p1 p2 p3 p4 : P),
    q2226868_strictly_between A p1 p4 p3 ->
    q2226868_angle A p1 p4 p2 = PI / 2 ->
    q2226868_angle A p1 p2 p3 = PI / 2 ->
    q2226868_dist A p2 p4 * q2226868_dist A p2 p4 =
      q2226868_dist A p1 p4 * q2226868_dist A p3 p4.
Admitted.
