(*
  Statement-only formalization of Thousand Theorems corpus artifact Q739403
  (thousand-theorems__rocq__Q739403), "Stewart's theorem": in an arbitrary
  real inner-product affine space, if the angle b-p-c is pi, a weighted sum
  of squared distances from a to b and c equals the corresponding product
  involving the cevian endpoint p. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q739403_real_inner_product_space (V : Type) : Type := {
  q739403_zero : V;
  q739403_add : V -> V -> V;
  q739403_neg : V -> V;
  q739403_smul : R -> V -> V;
  q739403_inner : V -> V -> R;

  q739403_add_assoc :
    forall x y z : V,
      q739403_add x (q739403_add y z) =
      q739403_add (q739403_add x y) z;
  q739403_add_comm :
    forall x y : V, q739403_add x y = q739403_add y x;
  q739403_add_zero :
    forall x : V, q739403_add x q739403_zero = x;
  q739403_add_neg :
    forall x : V,
      q739403_add x (q739403_neg x) = q739403_zero;

  q739403_one_smul :
    forall x : V, q739403_smul 1 x = x;
  q739403_mul_smul :
    forall (a b : R) (x : V),
      q739403_smul (a * b) x =
      q739403_smul a (q739403_smul b x);
  q739403_smul_add :
    forall (a : R) (x y : V),
      q739403_smul a (q739403_add x y) =
      q739403_add (q739403_smul a x) (q739403_smul a y);
  q739403_add_smul :
    forall (a b : R) (x : V),
      q739403_smul (a + b) x =
      q739403_add (q739403_smul a x) (q739403_smul b x);

  q739403_inner_add_left :
    forall x y z : V,
      q739403_inner (q739403_add x y) z =
      q739403_inner x z + q739403_inner y z;
  q739403_inner_smul_left :
    forall (a : R) (x y : V),
      q739403_inner (q739403_smul a x) y =
      a * q739403_inner x y;
  q739403_inner_symm :
    forall x y : V,
      q739403_inner x y = q739403_inner y x;
  q739403_inner_nonnegative :
    forall x : V, 0 <= q739403_inner x x;
  q739403_inner_eq_zero :
    forall x : V,
      q739403_inner x x = 0 <-> x = q739403_zero
}.

Arguments q739403_zero {V} _.
Arguments q739403_add {V} _ _ _.
Arguments q739403_neg {V} _ _.
Arguments q739403_smul {V} _ _ _.
Arguments q739403_inner {V} _ _ _.

Record q739403_affine_torsor
    (V P : Type)
    (E : q739403_real_inner_product_space V) : Type := {
  q739403_vadd : V -> P -> P;
  q739403_vsub : P -> P -> V;
  q739403_zero_vadd :
    forall p : P,
      q739403_vadd (q739403_zero E) p = p;
  q739403_add_vadd :
    forall (x y : V) (p : P),
      q739403_vadd (q739403_add E x y) p =
      q739403_vadd x (q739403_vadd y p);
  q739403_vsub_vadd :
    forall (x : V) (p : P),
      q739403_vsub (q739403_vadd x p) p = x;
  q739403_vadd_vsub :
    forall p q : P,
      q739403_vadd (q739403_vsub p q) q = p
}.

Arguments q739403_vadd {V P E} _ _ _.
Arguments q739403_vsub {V P E} _ _ _.

Definition q739403_norm
    {V : Type}
    (E : q739403_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q739403_inner E x x).

Definition q739403_dist
    {V P : Type}
    {E : q739403_real_inner_product_space V}
    (A : @q739403_affine_torsor V P E)
    (p q : P) : R :=
  q739403_norm E (q739403_vsub A p q).

Definition q739403_angle
    {V P : Type}
    {E : q739403_real_inner_product_space V}
    (A : @q739403_affine_torsor V P E)
    (p1 p2 p3 : P) : R :=
  let x := q739403_vsub A p1 p2 in
  let y := q739403_vsub A p3 p2 in
  acos
    (q739403_inner E x y /
      (q739403_norm E x * q739403_norm E y)).

Theorem EuclideanGeometry_dist_sq_mul_dist_add_dist_sq_mul_dist :
  forall (V P : Type)
         (E : q739403_real_inner_product_space V)
         (A : @q739403_affine_torsor V P E)
         (a b c p : P),
    q739403_angle A b p c = PI ->
    q739403_dist A a b * q739403_dist A a b *
        q739403_dist A c p +
      q739403_dist A a c * q739403_dist A a c *
        q739403_dist A b p =
    q739403_dist A b c *
      (q739403_dist A a p * q739403_dist A a p +
       q739403_dist A b p * q739403_dist A c p).
Admitted.
