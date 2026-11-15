(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1727461
  (thousand-theorems__rocq__Q1727461), "Intersecting secants theorem": in an
  arbitrary real inner-product affine space, two secants through a common
  point and meeting four cospherical points have equal products of distances
  from that point to their endpoints. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1727461_real_inner_product_space (V : Type) : Type := {
  q1727461_zero : V;
  q1727461_add : V -> V -> V;
  q1727461_neg : V -> V;
  q1727461_smul : R -> V -> V;
  q1727461_inner : V -> V -> R;

  q1727461_add_assoc :
    forall x y z : V,
      q1727461_add x (q1727461_add y z) =
      q1727461_add (q1727461_add x y) z;
  q1727461_add_comm :
    forall x y : V, q1727461_add x y = q1727461_add y x;
  q1727461_add_zero :
    forall x : V, q1727461_add x q1727461_zero = x;
  q1727461_add_neg :
    forall x : V, q1727461_add x (q1727461_neg x) = q1727461_zero;

  q1727461_one_smul :
    forall x : V, q1727461_smul 1 x = x;
  q1727461_mul_smul :
    forall (a b : R) (x : V),
      q1727461_smul (a * b) x =
      q1727461_smul a (q1727461_smul b x);
  q1727461_smul_add :
    forall (a : R) (x y : V),
      q1727461_smul a (q1727461_add x y) =
      q1727461_add (q1727461_smul a x) (q1727461_smul a y);
  q1727461_add_smul :
    forall (a b : R) (x : V),
      q1727461_smul (a + b) x =
      q1727461_add (q1727461_smul a x) (q1727461_smul b x);

  q1727461_inner_add_left :
    forall x y z : V,
      q1727461_inner (q1727461_add x y) z =
      q1727461_inner x z + q1727461_inner y z;
  q1727461_inner_smul_left :
    forall (a : R) (x y : V),
      q1727461_inner (q1727461_smul a x) y =
      a * q1727461_inner x y;
  q1727461_inner_symm :
    forall x y : V, q1727461_inner x y = q1727461_inner y x;
  q1727461_inner_nonnegative :
    forall x : V, 0 <= q1727461_inner x x;
  q1727461_inner_eq_zero :
    forall x : V,
      q1727461_inner x x = 0 <-> x = q1727461_zero
}.

Arguments q1727461_zero {V} _.
Arguments q1727461_add {V} _ _ _.
Arguments q1727461_neg {V} _ _.
Arguments q1727461_smul {V} _ _ _.
Arguments q1727461_inner {V} _ _ _.

Record q1727461_affine_torsor
    (V P : Type) (E : q1727461_real_inner_product_space V) : Type := {
  q1727461_vadd : V -> P -> P;
  q1727461_vsub : P -> P -> V;
  q1727461_zero_vadd :
    forall p : P, q1727461_vadd (q1727461_zero E) p = p;
  q1727461_add_vadd :
    forall (x y : V) (p : P),
      q1727461_vadd (q1727461_add E x y) p =
      q1727461_vadd x (q1727461_vadd y p);
  q1727461_vsub_vadd :
    forall (x : V) (p : P),
      q1727461_vsub (q1727461_vadd x p) p = x;
  q1727461_vadd_vsub :
    forall p q : P,
      q1727461_vadd (q1727461_vsub p q) q = p
}.

Arguments q1727461_vadd {V P E} _ _ _.
Arguments q1727461_vsub {V P E} _ _ _.

Definition q1727461_norm
    {V : Type}
    (E : q1727461_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q1727461_inner E x x).

Definition q1727461_dist
    {V P : Type}
    {E : q1727461_real_inner_product_space V}
    (A : @q1727461_affine_torsor V P E)
    (p q : P) : R :=
  q1727461_norm E (q1727461_vsub A p q).

Definition q1727461_cospherical_four
    {V P : Type}
    {E : q1727461_real_inner_product_space V}
    (A : @q1727461_affine_torsor V P E)
    (a b c d : P) : Prop :=
  exists (center : P) (radius : R),
    q1727461_dist A a center = radius /\
    q1727461_dist A b center = radius /\
    q1727461_dist A c center = radius /\
    q1727461_dist A d center = radius.

Definition q1727461_angle
    {V P : Type}
    {E : q1727461_real_inner_product_space V}
    (A : @q1727461_affine_torsor V P E)
    (a p b : P) : R :=
  let x := q1727461_vsub A a p in
  let y := q1727461_vsub A b p in
  acos
    (q1727461_inner E x y /
      (q1727461_norm E x * q1727461_norm E y)).

Theorem EuclideanGeometry_mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_zero :
  forall (V P : Type)
         (E : q1727461_real_inner_product_space V)
         (A : @q1727461_affine_torsor V P E)
         (a b c d p : P),
    q1727461_cospherical_four A a b c d ->
    a <> b ->
    c <> d ->
    q1727461_angle A a p b = 0 ->
    q1727461_angle A c p d = 0 ->
    q1727461_dist A a p * q1727461_dist A b p =
      q1727461_dist A c p * q1727461_dist A d p.
Admitted.
