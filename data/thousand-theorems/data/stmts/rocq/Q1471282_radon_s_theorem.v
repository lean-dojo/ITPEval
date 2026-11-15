(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1471282
  (thousand-theorems__rocq__Q1471282), "Radon's theorem": every affinely
  dependent family over a linearly ordered field has a subset whose convex
  hull meets the convex hull of its complement. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1471282_linear_ordered_field (K : Type) : Type := {
  q1471282_zero : K;
  q1471282_one : K;
  q1471282_add : K -> K -> K;
  q1471282_mul : K -> K -> K;
  q1471282_neg : K -> K;
  q1471282_inv : K -> K;
  q1471282_le : K -> K -> Prop;
  q1471282_zero_ne_one :
    q1471282_zero <> q1471282_one;
  q1471282_add_assoc :
    forall x y z : K,
      q1471282_add x (q1471282_add y z) =
      q1471282_add (q1471282_add x y) z;
  q1471282_add_comm :
    forall x y : K,
      q1471282_add x y = q1471282_add y x;
  q1471282_add_zero :
    forall x : K,
      q1471282_add x q1471282_zero = x;
  q1471282_add_neg :
    forall x : K,
      q1471282_add x (q1471282_neg x) = q1471282_zero;
  q1471282_mul_assoc :
    forall x y z : K,
      q1471282_mul x (q1471282_mul y z) =
      q1471282_mul (q1471282_mul x y) z;
  q1471282_mul_comm :
    forall x y : K,
      q1471282_mul x y = q1471282_mul y x;
  q1471282_mul_one :
    forall x : K,
      q1471282_mul x q1471282_one = x;
  q1471282_left_distrib :
    forall x y z : K,
      q1471282_mul x (q1471282_add y z) =
      q1471282_add
        (q1471282_mul x y) (q1471282_mul x z);
  q1471282_inv_zero :
    q1471282_inv q1471282_zero = q1471282_zero;
  q1471282_mul_inv :
    forall x : K,
      x <> q1471282_zero ->
      q1471282_mul x (q1471282_inv x) = q1471282_one;
  q1471282_le_refl :
    forall x : K, q1471282_le x x;
  q1471282_le_trans :
    forall x y z : K,
      q1471282_le x y ->
      q1471282_le y z ->
      q1471282_le x z;
  q1471282_le_antisym :
    forall x y : K,
      q1471282_le x y ->
      q1471282_le y x ->
      x = y;
  q1471282_le_total :
    forall x y : K,
      q1471282_le x y \/ q1471282_le y x;
  q1471282_le_decidable :
    forall x y : K,
      {q1471282_le x y} + {~ q1471282_le x y};
  q1471282_add_le_add_left :
    forall x y z : K,
      q1471282_le x y ->
      q1471282_le
        (q1471282_add z x) (q1471282_add z y);
  q1471282_mul_nonnegative :
    forall x y : K,
      q1471282_le q1471282_zero x ->
      q1471282_le q1471282_zero y ->
      q1471282_le q1471282_zero (q1471282_mul x y)
}.

Arguments q1471282_zero {K} _.
Arguments q1471282_one {K} _.
Arguments q1471282_add {K} _ _ _.
Arguments q1471282_mul {K} _ _ _.
Arguments q1471282_neg {K} _ _.
Arguments q1471282_inv {K} _ _.
Arguments q1471282_le {K} _ _ _.

Record q1471282_module
    (K E : Type)
    (fld : q1471282_linear_ordered_field K) : Type := {
  q1471282_vzero : E;
  q1471282_vadd : E -> E -> E;
  q1471282_vneg : E -> E;
  q1471282_smul : K -> E -> E;
  q1471282_vadd_assoc :
    forall x y z : E,
      q1471282_vadd x (q1471282_vadd y z) =
      q1471282_vadd (q1471282_vadd x y) z;
  q1471282_vadd_comm :
    forall x y : E,
      q1471282_vadd x y = q1471282_vadd y x;
  q1471282_vadd_zero :
    forall x : E,
      q1471282_vadd x q1471282_vzero = x;
  q1471282_vadd_neg :
    forall x : E,
      q1471282_vadd x (q1471282_vneg x) = q1471282_vzero;
  q1471282_one_smul :
    forall x : E,
      q1471282_smul (q1471282_one fld) x = x;
  q1471282_mul_smul :
    forall (a b : K) (x : E),
      q1471282_smul (q1471282_mul fld a b) x =
      q1471282_smul a (q1471282_smul b x);
  q1471282_add_smul :
    forall (a b : K) (x : E),
      q1471282_smul (q1471282_add fld a b) x =
      q1471282_vadd (q1471282_smul a x) (q1471282_smul b x);
  q1471282_smul_add :
    forall (a : K) (x y : E),
      q1471282_smul a (q1471282_vadd x y) =
      q1471282_vadd (q1471282_smul a x) (q1471282_smul a y)
}.

Arguments q1471282_vzero {K E fld} _.
Arguments q1471282_vadd {K E fld} _ _ _.
Arguments q1471282_vneg {K E fld} _ _.
Arguments q1471282_smul {K E fld} _ _ _.

Definition q1471282_set (A : Type) : Type := A -> Prop.

Definition q1471282_subset {A : Type}
    (S T : q1471282_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q1471282_complement {A : Type}
    (S : q1471282_set A) : q1471282_set A :=
  fun x => ~ S x.

Definition q1471282_image {A B : Type}
    (f : A -> B)
    (S : q1471282_set A) : q1471282_set B :=
  fun y => exists x : A, S x /\ f x = y.

Fixpoint q1471282_scalar_sum
    {K I : Type}
    (fld : q1471282_linear_ordered_field K)
    (indices : list I)
    (weights : I -> K) : K :=
  match indices with
  | nil => q1471282_zero fld
  | cons i rest =>
      q1471282_add fld
        (weights i) (q1471282_scalar_sum fld rest weights)
  end.

Fixpoint q1471282_weighted_sum
    {K E I : Type}
    {fld : q1471282_linear_ordered_field K}
    (V : @q1471282_module K E fld)
    (indices : list I)
    (weights : I -> K)
    (points : I -> E) : E :=
  match indices with
  | nil => q1471282_vzero V
  | cons i rest =>
      q1471282_vadd V
        (q1471282_smul V (weights i) (points i))
        (q1471282_weighted_sum V rest weights points)
  end.

Definition q1471282_affine_independent
    {K E I : Type}
    (fld : q1471282_linear_ordered_field K)
    (V : @q1471282_module K E fld)
    (f : I -> E) : Prop :=
  forall (weights : I -> K) (support : list I),
    NoDup support ->
    q1471282_scalar_sum fld support weights =
      q1471282_zero fld ->
    q1471282_weighted_sum V support weights f =
      q1471282_vzero V ->
    forall i : I,
      In i support ->
      weights i = q1471282_zero fld.

Definition q1471282_convex
    {K E : Type}
    (fld : q1471282_linear_ordered_field K)
    (V : @q1471282_module K E fld)
    (S : q1471282_set E) : Prop :=
  forall (x y : E) (a b : K),
    S x ->
    S y ->
    q1471282_le fld (q1471282_zero fld) a ->
    q1471282_le fld (q1471282_zero fld) b ->
    q1471282_add fld a b = q1471282_one fld ->
    S
      (q1471282_vadd V
        (q1471282_smul V a x)
        (q1471282_smul V b y)).

Definition q1471282_convex_hull
    {K E : Type}
    (fld : q1471282_linear_ordered_field K)
    (V : @q1471282_module K E fld)
    (S : q1471282_set E) : q1471282_set E :=
  fun x =>
    forall C : q1471282_set E,
      @q1471282_convex K E fld V C ->
      q1471282_subset S C ->
      C x.

Module Convex.

Theorem radon_partition :
  forall (K E I : Type)
         (fld : q1471282_linear_ordered_field K)
         (V : @q1471282_module K E fld)
         (f : I -> E),
    ~ @q1471282_affine_independent K E I fld V f ->
    exists S : q1471282_set I,
    exists x : E,
      @q1471282_convex_hull K E fld V (q1471282_image f S) x /\
      @q1471282_convex_hull K E fld V
        (q1471282_image f (q1471282_complement S)) x.
Admitted.

End Convex.
