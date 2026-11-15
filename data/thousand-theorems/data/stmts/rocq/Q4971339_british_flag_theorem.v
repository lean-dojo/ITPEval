(*
  Statement-only formalization of Thousand Theorems corpus artifact Q4971339
  (thousand-theorems__rocq__Q4971339), "British flag theorem": in an arbitrary
  real inner-product affine space, a possibly degenerate parallelogram with a
  right angle at one vertex has equal sums of squared distances from any point
  to its two pairs of opposite vertices. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q4971339_real_inner_product_space (V : Type) : Type := {
  q4971339_zero : V;
  q4971339_add : V -> V -> V;
  q4971339_neg : V -> V;
  q4971339_smul : R -> V -> V;
  q4971339_inner : V -> V -> R;

  q4971339_add_assoc :
    forall x y z : V,
      q4971339_add x (q4971339_add y z) =
      q4971339_add (q4971339_add x y) z;
  q4971339_add_comm :
    forall x y : V, q4971339_add x y = q4971339_add y x;
  q4971339_add_zero :
    forall x : V, q4971339_add x q4971339_zero = x;
  q4971339_add_neg :
    forall x : V,
      q4971339_add x (q4971339_neg x) = q4971339_zero;

  q4971339_one_smul :
    forall x : V, q4971339_smul 1 x = x;
  q4971339_mul_smul :
    forall (a b : R) (x : V),
      q4971339_smul (a * b) x =
      q4971339_smul a (q4971339_smul b x);
  q4971339_smul_add :
    forall (a : R) (x y : V),
      q4971339_smul a (q4971339_add x y) =
      q4971339_add (q4971339_smul a x) (q4971339_smul a y);
  q4971339_add_smul :
    forall (a b : R) (x : V),
      q4971339_smul (a + b) x =
      q4971339_add (q4971339_smul a x) (q4971339_smul b x);

  q4971339_inner_add_left :
    forall x y z : V,
      q4971339_inner (q4971339_add x y) z =
      q4971339_inner x z + q4971339_inner y z;
  q4971339_inner_smul_left :
    forall (a : R) (x y : V),
      q4971339_inner (q4971339_smul a x) y =
      a * q4971339_inner x y;
  q4971339_inner_symm :
    forall x y : V,
      q4971339_inner x y = q4971339_inner y x;
  q4971339_inner_nonnegative :
    forall x : V, 0 <= q4971339_inner x x;
  q4971339_inner_eq_zero :
    forall x : V,
      q4971339_inner x x = 0 <-> x = q4971339_zero
}.

Arguments q4971339_zero {V} _.
Arguments q4971339_add {V} _ _ _.
Arguments q4971339_neg {V} _ _.
Arguments q4971339_smul {V} _ _ _.
Arguments q4971339_inner {V} _ _ _.

Record q4971339_affine_torsor
    (V P : Type)
    (E : q4971339_real_inner_product_space V) : Type := {
  q4971339_vadd : V -> P -> P;
  q4971339_vsub : P -> P -> V;
  q4971339_zero_vadd :
    forall p : P,
      q4971339_vadd (q4971339_zero E) p = p;
  q4971339_add_vadd :
    forall (x y : V) (p : P),
      q4971339_vadd (q4971339_add E x y) p =
      q4971339_vadd x (q4971339_vadd y p);
  q4971339_vsub_vadd :
    forall (x : V) (p : P),
      q4971339_vsub (q4971339_vadd x p) p = x;
  q4971339_vadd_vsub :
    forall p q : P,
      q4971339_vadd (q4971339_vsub p q) q = p
}.

Arguments q4971339_vadd {V P E} _ _ _.
Arguments q4971339_vsub {V P E} _ _ _.

Definition q4971339_norm
    {V : Type}
    (E : q4971339_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q4971339_inner E x x).

Definition q4971339_dist
    {V P : Type}
    {E : q4971339_real_inner_product_space V}
    (A : @q4971339_affine_torsor V P E)
    (p q : P) : R :=
  q4971339_norm E (q4971339_vsub A p q).

Definition q4971339_midpoint
    {V P : Type}
    {E : q4971339_real_inner_product_space V}
    (A : @q4971339_affine_torsor V P E)
    (p q : P) : P :=
  q4971339_vadd A
    (q4971339_smul E (1 / 2) (q4971339_vsub A p q)) q.

Definition q4971339_angle
    {V P : Type}
    {E : q4971339_real_inner_product_space V}
    (A : @q4971339_affine_torsor V P E)
    (p1 p2 p3 : P) : R :=
  let x := q4971339_vsub A p1 p2 in
  let y := q4971339_vsub A p3 p2 in
  acos
    (q4971339_inner E x y /
      (q4971339_norm E x * q4971339_norm E y)).

Theorem EuclideanGeometry_dist_sq_add_dist_sq_eq_dist_sq_add_dist_sq_of_angle_eq_pi_div_two :
  forall (V P : Type)
         (E : q4971339_real_inner_product_space V)
         (A : @q4971339_affine_torsor V P E)
         (a b c d p : P),
    q4971339_midpoint A a c = q4971339_midpoint A b d ->
    q4971339_angle A b a d = PI / 2 ->
    q4971339_dist A p a * q4971339_dist A p a +
      q4971339_dist A p c * q4971339_dist A p c =
    q4971339_dist A p b * q4971339_dist A p b +
      q4971339_dist A p d * q4971339_dist A p d.
Admitted.
