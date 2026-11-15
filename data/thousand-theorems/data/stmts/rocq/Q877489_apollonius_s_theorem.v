(*
  Statement-only formalization of Thousand Theorems corpus artifact Q877489
  (thousand-theorems__rocq__Q877489), "Apollonius's theorem": in an arbitrary
  real inner-product affine space, the sum of the squared distances from a
  point to two endpoints equals twice the sum of the squared distance to their
  midpoint and the squared half-distance between the endpoints. This file
  contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q877489_real_inner_product_space (V : Type) : Type := {
  q877489_zero : V;
  q877489_add : V -> V -> V;
  q877489_neg : V -> V;
  q877489_smul : R -> V -> V;
  q877489_inner : V -> V -> R;

  q877489_add_assoc :
    forall x y z : V,
      q877489_add x (q877489_add y z) =
      q877489_add (q877489_add x y) z;
  q877489_add_comm :
    forall x y : V, q877489_add x y = q877489_add y x;
  q877489_add_zero :
    forall x : V, q877489_add x q877489_zero = x;
  q877489_add_neg :
    forall x : V,
      q877489_add x (q877489_neg x) = q877489_zero;

  q877489_one_smul :
    forall x : V, q877489_smul 1 x = x;
  q877489_mul_smul :
    forall (a b : R) (x : V),
      q877489_smul (a * b) x =
      q877489_smul a (q877489_smul b x);
  q877489_smul_add :
    forall (a : R) (x y : V),
      q877489_smul a (q877489_add x y) =
      q877489_add (q877489_smul a x) (q877489_smul a y);
  q877489_add_smul :
    forall (a b : R) (x : V),
      q877489_smul (a + b) x =
      q877489_add (q877489_smul a x) (q877489_smul b x);

  q877489_inner_add_left :
    forall x y z : V,
      q877489_inner (q877489_add x y) z =
      q877489_inner x z + q877489_inner y z;
  q877489_inner_smul_left :
    forall (a : R) (x y : V),
      q877489_inner (q877489_smul a x) y =
      a * q877489_inner x y;
  q877489_inner_symm :
    forall x y : V, q877489_inner x y = q877489_inner y x;
  q877489_inner_nonnegative :
    forall x : V, 0 <= q877489_inner x x;
  q877489_inner_eq_zero :
    forall x : V,
      q877489_inner x x = 0 <-> x = q877489_zero
}.

Arguments q877489_zero {V} _.
Arguments q877489_add {V} _ _ _.
Arguments q877489_neg {V} _ _.
Arguments q877489_smul {V} _ _ _.
Arguments q877489_inner {V} _ _ _.

Record q877489_affine_torsor
    (V P : Type)
    (E : q877489_real_inner_product_space V) : Type := {
  q877489_vadd : V -> P -> P;
  q877489_vsub : P -> P -> V;
  q877489_zero_vadd :
    forall p : P, q877489_vadd (q877489_zero E) p = p;
  q877489_add_vadd :
    forall (x y : V) (p : P),
      q877489_vadd (q877489_add E x y) p =
      q877489_vadd x (q877489_vadd y p);
  q877489_vsub_vadd :
    forall (x : V) (p : P),
      q877489_vsub (q877489_vadd x p) p = x;
  q877489_vadd_vsub :
    forall p q : P,
      q877489_vadd (q877489_vsub p q) q = p
}.

Arguments q877489_vadd {V P E} _ _ _.
Arguments q877489_vsub {V P E} _ _ _.

Definition q877489_norm
    {V : Type}
    (E : q877489_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q877489_inner E x x).

Definition q877489_dist
    {V P : Type}
    {E : q877489_real_inner_product_space V}
    (A : @q877489_affine_torsor V P E)
    (p q : P) : R :=
  q877489_norm E (q877489_vsub A p q).

Definition q877489_midpoint
    {V P : Type}
    {E : q877489_real_inner_product_space V}
    (A : @q877489_affine_torsor V P E)
    (p q : P) : P :=
  q877489_vadd A
    (q877489_smul E (1 / 2) (q877489_vsub A q p))
    p.

Definition q877489_square (x : R) : R := x * x.

Theorem EuclideanGeometry_dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq :
  forall (V P : Type)
         (E : q877489_real_inner_product_space V)
         (A : @q877489_affine_torsor V P E)
         (a b c : P),
    q877489_square (q877489_dist A a b) +
      q877489_square (q877489_dist A a c) =
    2 *
      (q877489_square
        (q877489_dist A a (q877489_midpoint A b c)) +
       q877489_square (q877489_dist A b c / 2)).
Admitted.
