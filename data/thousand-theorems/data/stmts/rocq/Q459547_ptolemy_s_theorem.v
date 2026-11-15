(*
  Statement-only formalization of Thousand Theorems corpus artifact Q459547
  (thousand-theorems__rocq__Q459547), "Ptolemy's theorem": in an arbitrary
  real inner-product affine space, four cospherical points whose diagonals
  pass through a common point satisfy Ptolemy's distance identity. This file
  contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q459547_real_inner_product_space (V : Type) : Type := {
  q459547_zero : V;
  q459547_add : V -> V -> V;
  q459547_neg : V -> V;
  q459547_smul : R -> V -> V;
  q459547_inner : V -> V -> R;

  q459547_add_assoc :
    forall x y z : V,
      q459547_add x (q459547_add y z) =
      q459547_add (q459547_add x y) z;
  q459547_add_comm :
    forall x y : V, q459547_add x y = q459547_add y x;
  q459547_add_zero :
    forall x : V, q459547_add x q459547_zero = x;
  q459547_add_neg :
    forall x : V, q459547_add x (q459547_neg x) = q459547_zero;

  q459547_one_smul :
    forall x : V, q459547_smul 1 x = x;
  q459547_mul_smul :
    forall (a b : R) (x : V),
      q459547_smul (a * b) x =
      q459547_smul a (q459547_smul b x);
  q459547_smul_add :
    forall (a : R) (x y : V),
      q459547_smul a (q459547_add x y) =
      q459547_add (q459547_smul a x) (q459547_smul a y);
  q459547_add_smul :
    forall (a b : R) (x : V),
      q459547_smul (a + b) x =
      q459547_add (q459547_smul a x) (q459547_smul b x);

  q459547_inner_add_left :
    forall x y z : V,
      q459547_inner (q459547_add x y) z =
      q459547_inner x z + q459547_inner y z;
  q459547_inner_smul_left :
    forall (a : R) (x y : V),
      q459547_inner (q459547_smul a x) y =
      a * q459547_inner x y;
  q459547_inner_symm :
    forall x y : V, q459547_inner x y = q459547_inner y x;
  q459547_inner_nonnegative :
    forall x : V, 0 <= q459547_inner x x;
  q459547_inner_eq_zero :
    forall x : V,
      q459547_inner x x = 0 <-> x = q459547_zero
}.

Arguments q459547_zero {V} _.
Arguments q459547_add {V} _ _ _.
Arguments q459547_neg {V} _ _.
Arguments q459547_smul {V} _ _ _.
Arguments q459547_inner {V} _ _ _.

Record q459547_affine_torsor
    (V P : Type) (E : q459547_real_inner_product_space V) : Type := {
  q459547_vadd : V -> P -> P;
  q459547_vsub : P -> P -> V;
  q459547_zero_vadd :
    forall p : P, q459547_vadd (q459547_zero E) p = p;
  q459547_add_vadd :
    forall (x y : V) (p : P),
      q459547_vadd (q459547_add E x y) p =
      q459547_vadd x (q459547_vadd y p);
  q459547_vsub_vadd :
    forall (x : V) (p : P),
      q459547_vsub (q459547_vadd x p) p = x;
  q459547_vadd_vsub :
    forall p q : P,
      q459547_vadd (q459547_vsub p q) q = p
}.

Arguments q459547_vadd {V P E} _ _ _.
Arguments q459547_vsub {V P E} _ _ _.

Definition q459547_norm
    {V : Type}
    (E : q459547_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q459547_inner E x x).

Definition q459547_dist
    {V P : Type}
    {E : q459547_real_inner_product_space V}
    (A : @q459547_affine_torsor V P E)
    (p q : P) : R :=
  q459547_norm E (q459547_vsub A p q).

Definition q459547_cospherical_four
    {V P : Type}
    {E : q459547_real_inner_product_space V}
    (A : @q459547_affine_torsor V P E)
    (a b c d : P) : Prop :=
  exists (center : P) (radius : R),
    q459547_dist A a center = radius /\
    q459547_dist A b center = radius /\
    q459547_dist A c center = radius /\
    q459547_dist A d center = radius.

Definition q459547_angle
    {V P : Type}
    {E : q459547_real_inner_product_space V}
    (A : @q459547_affine_torsor V P E)
    (a p c : P) : R :=
  let x := q459547_vsub A a p in
  let y := q459547_vsub A c p in
  acos
    (q459547_inner E x y /
      (q459547_norm E x * q459547_norm E y)).

Theorem EuclideanGeometry_mul_dist_add_mul_dist_eq_mul_dist_of_cospherical :
  forall (V P : Type)
         (E : q459547_real_inner_product_space V)
         (A : @q459547_affine_torsor V P E)
         (a b c d p : P),
    q459547_cospherical_four A a b c d ->
    q459547_angle A a p c = PI ->
    q459547_angle A b p d = PI ->
    q459547_dist A a b * q459547_dist A c d +
      q459547_dist A b c * q459547_dist A d a =
    q459547_dist A a c * q459547_dist A b d.
Admitted.
