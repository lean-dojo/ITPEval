(*
  Statement-only formalization of Thousand Theorems corpus artifact Q3527215
  (thousand-theorems__rocq__Q3527215), "Hilbert projection theorem": every
  point in a real inner-product space has a closest point in each nonempty
  complete convex subset, attaining the infimum of the distance.
  This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q3527215_real_inner_product_space (F : Type) : Type := {
  q3527215_zero : F;
  q3527215_add : F -> F -> F;
  q3527215_neg : F -> F;
  q3527215_smul : R -> F -> F;
  q3527215_inner : F -> F -> R;

  q3527215_add_assoc :
    forall x y z : F,
      q3527215_add x (q3527215_add y z) =
      q3527215_add (q3527215_add x y) z;
  q3527215_add_comm :
    forall x y : F, q3527215_add x y = q3527215_add y x;
  q3527215_add_zero :
    forall x : F, q3527215_add x q3527215_zero = x;
  q3527215_add_neg :
    forall x : F,
      q3527215_add x (q3527215_neg x) = q3527215_zero;

  q3527215_one_smul :
    forall x : F, q3527215_smul 1 x = x;
  q3527215_mul_smul :
    forall (a b : R) (x : F),
      q3527215_smul (a * b) x =
      q3527215_smul a (q3527215_smul b x);
  q3527215_add_smul :
    forall (a b : R) (x : F),
      q3527215_smul (a + b) x =
      q3527215_add
        (q3527215_smul a x) (q3527215_smul b x);
  q3527215_smul_add :
    forall (a : R) (x y : F),
      q3527215_smul a (q3527215_add x y) =
      q3527215_add
        (q3527215_smul a x) (q3527215_smul a y);
  q3527215_zero_smul :
    forall x : F, q3527215_smul 0 x = q3527215_zero;
  q3527215_smul_zero :
    forall a : R, q3527215_smul a q3527215_zero = q3527215_zero;

  q3527215_inner_add_left :
    forall x y z : F,
      q3527215_inner (q3527215_add x y) z =
      q3527215_inner x z + q3527215_inner y z;
  q3527215_inner_smul_left :
    forall (a : R) (x y : F),
      q3527215_inner (q3527215_smul a x) y =
      a * q3527215_inner x y;
  q3527215_inner_symm :
    forall x y : F, q3527215_inner x y = q3527215_inner y x;
  q3527215_inner_nonnegative :
    forall x : F, 0 <= q3527215_inner x x;
  q3527215_inner_eq_zero :
    forall x : F,
      q3527215_inner x x = 0 <-> x = q3527215_zero
}.

Arguments q3527215_zero {F} _.
Arguments q3527215_add {F} _ _ _.
Arguments q3527215_neg {F} _ _.
Arguments q3527215_smul {F} _ _ _.
Arguments q3527215_inner {F} _ _ _.

Definition q3527215_sub
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (x y : F) : F :=
  q3527215_add H x (q3527215_neg H y).

Definition q3527215_norm
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (x : F) : R :=
  sqrt (q3527215_inner H x x).

Definition q3527215_sequence_converges
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (sequence : nat -> F)
    (limit : F) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q3527215_norm H
          (q3527215_sub H (sequence n) limit) < epsilon.

Definition q3527215_sequence_cauchy
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (sequence : nat -> F) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q3527215_norm H
          (q3527215_sub H (sequence m) (sequence n)) < epsilon.

Definition q3527215_nonempty
    {F : Type}
    (K : F -> Prop) : Prop :=
  exists x : F, K x.

Definition q3527215_is_complete
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (K : F -> Prop) : Prop :=
  forall sequence : nat -> F,
    (forall n : nat, K (sequence n)) ->
    q3527215_sequence_cauchy H sequence ->
    exists limit : F,
      K limit /\
      q3527215_sequence_converges H sequence limit.

Definition q3527215_is_convex
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (K : F -> Prop) : Prop :=
  forall (x y : F) (a b : R),
    K x ->
    K y ->
    0 <= a ->
    0 <= b ->
    a + b = 1 ->
    K
      (q3527215_add H
        (q3527215_smul H a x)
        (q3527215_smul H b y)).

Definition q3527215_is_distance_infimum
    {F : Type}
    (H : q3527215_real_inner_product_space F)
    (K : F -> Prop)
    (u : F)
    (distance_infimum : R) : Prop :=
  (forall w : F,
    K w ->
    distance_infimum <=
      q3527215_norm H (q3527215_sub H u w)) /\
  forall lower_bound : R,
    (forall w : F,
      K w ->
      lower_bound <=
        q3527215_norm H (q3527215_sub H u w)) ->
    lower_bound <= distance_infimum.

Theorem exists_norm_eq_iInf_of_complete_convex :
  forall (F : Type)
         (H : q3527215_real_inner_product_space F)
         (K : F -> Prop),
    q3527215_nonempty K ->
    q3527215_is_complete H K ->
    q3527215_is_convex H K ->
    forall u : F,
      exists v : F,
        K v /\
        q3527215_is_distance_infimum H K u
          (q3527215_norm H (q3527215_sub H u v)).
Admitted.
