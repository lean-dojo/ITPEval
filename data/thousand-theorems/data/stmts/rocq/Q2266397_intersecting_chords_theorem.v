(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2266397
  (thousand-theorems__rocq__Q2266397), "Intersecting chords theorem": in an
  arbitrary real inner-product affine space, four cospherical points lying on
  two straight angles through a common point have equal products of distances
  from that point to the paired endpoints. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q2266397_real_inner_product_space (V : Type) : Type := {
  q2266397_zero : V;
  q2266397_add : V -> V -> V;
  q2266397_neg : V -> V;
  q2266397_smul : R -> V -> V;
  q2266397_inner : V -> V -> R;

  q2266397_add_assoc :
    forall x y z : V,
      q2266397_add x (q2266397_add y z) =
      q2266397_add (q2266397_add x y) z;
  q2266397_add_comm :
    forall x y : V, q2266397_add x y = q2266397_add y x;
  q2266397_add_zero :
    forall x : V, q2266397_add x q2266397_zero = x;
  q2266397_add_neg :
    forall x : V, q2266397_add x (q2266397_neg x) = q2266397_zero;

  q2266397_one_smul :
    forall x : V, q2266397_smul 1 x = x;
  q2266397_mul_smul :
    forall (a b : R) (x : V),
      q2266397_smul (a * b) x =
      q2266397_smul a (q2266397_smul b x);
  q2266397_smul_add :
    forall (a : R) (x y : V),
      q2266397_smul a (q2266397_add x y) =
      q2266397_add (q2266397_smul a x) (q2266397_smul a y);
  q2266397_add_smul :
    forall (a b : R) (x : V),
      q2266397_smul (a + b) x =
      q2266397_add (q2266397_smul a x) (q2266397_smul b x);

  q2266397_inner_add_left :
    forall x y z : V,
      q2266397_inner (q2266397_add x y) z =
      q2266397_inner x z + q2266397_inner y z;
  q2266397_inner_smul_left :
    forall (a : R) (x y : V),
      q2266397_inner (q2266397_smul a x) y =
      a * q2266397_inner x y;
  q2266397_inner_symm :
    forall x y : V, q2266397_inner x y = q2266397_inner y x;
  q2266397_inner_nonnegative :
    forall x : V, 0 <= q2266397_inner x x;
  q2266397_inner_eq_zero :
    forall x : V,
      q2266397_inner x x = 0 <-> x = q2266397_zero
}.

Arguments q2266397_zero {V} _.
Arguments q2266397_add {V} _ _ _.
Arguments q2266397_neg {V} _ _.
Arguments q2266397_smul {V} _ _ _.
Arguments q2266397_inner {V} _ _ _.

Record q2266397_affine_torsor
    (V P : Type) (E : q2266397_real_inner_product_space V) : Type := {
  q2266397_vadd : V -> P -> P;
  q2266397_vsub : P -> P -> V;
  q2266397_zero_vadd :
    forall p : P, q2266397_vadd (q2266397_zero E) p = p;
  q2266397_add_vadd :
    forall (x y : V) (p : P),
      q2266397_vadd (q2266397_add E x y) p =
      q2266397_vadd x (q2266397_vadd y p);
  q2266397_vsub_vadd :
    forall (x : V) (p : P),
      q2266397_vsub (q2266397_vadd x p) p = x;
  q2266397_vadd_vsub :
    forall p q : P,
      q2266397_vadd (q2266397_vsub p q) q = p
}.

Arguments q2266397_vadd {V P E} _ _ _.
Arguments q2266397_vsub {V P E} _ _ _.

Definition q2266397_norm
    {V : Type}
    (E : q2266397_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q2266397_inner E x x).

Definition q2266397_dist
    {V P : Type}
    {E : q2266397_real_inner_product_space V}
    (A : @q2266397_affine_torsor V P E)
    (p q : P) : R :=
  q2266397_norm E (q2266397_vsub A p q).

Definition q2266397_cospherical_four
    {V P : Type}
    {E : q2266397_real_inner_product_space V}
    (A : @q2266397_affine_torsor V P E)
    (a b c d : P) : Prop :=
  exists (center : P) (radius : R),
    q2266397_dist A a center = radius /\
    q2266397_dist A b center = radius /\
    q2266397_dist A c center = radius /\
    q2266397_dist A d center = radius.

Definition q2266397_angle
    {V P : Type}
    {E : q2266397_real_inner_product_space V}
    (A : @q2266397_affine_torsor V P E)
    (a p b : P) : R :=
  let x := q2266397_vsub A a p in
  let y := q2266397_vsub A b p in
  acos
    (q2266397_inner E x y /
      (q2266397_norm E x * q2266397_norm E y)).

Theorem EuclideanGeometry_mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi :
  forall (V P : Type)
         (E : q2266397_real_inner_product_space V)
         (A : @q2266397_affine_torsor V P E)
         (a b c d p : P),
    q2266397_cospherical_four A a b c d ->
    q2266397_angle A a p b = PI ->
    q2266397_angle A c p d = PI ->
    q2266397_dist A a p * q2266397_dist A b p =
      q2266397_dist A c p * q2266397_dist A d p.
Admitted.
