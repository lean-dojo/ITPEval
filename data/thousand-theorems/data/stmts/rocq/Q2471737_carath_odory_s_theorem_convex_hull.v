(*
  Statement-only formalization of Thousand Theorems corpus artifact Q2471737
  (thousand-theorems__rocq__Q2471737), "Carathéodory's theorem (convex hull)":
  over a linearly ordered field, the convex hull of a set is the union of the
  convex hulls of its finite affine-independent subsets. This file contains no
  proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q2471737_linear_ordered_field (K : Type) : Type := {
  q2471737_zero : K;
  q2471737_one : K;
  q2471737_add : K -> K -> K;
  q2471737_mul : K -> K -> K;
  q2471737_neg : K -> K;
  q2471737_inv : K -> K;
  q2471737_le : K -> K -> Prop;
  q2471737_zero_ne_one :
    q2471737_zero <> q2471737_one;
  q2471737_add_assoc :
    forall x y z : K,
      q2471737_add x (q2471737_add y z) =
      q2471737_add (q2471737_add x y) z;
  q2471737_add_comm :
    forall x y : K,
      q2471737_add x y = q2471737_add y x;
  q2471737_add_zero :
    forall x : K,
      q2471737_add x q2471737_zero = x;
  q2471737_add_neg :
    forall x : K,
      q2471737_add x (q2471737_neg x) = q2471737_zero;
  q2471737_mul_assoc :
    forall x y z : K,
      q2471737_mul x (q2471737_mul y z) =
      q2471737_mul (q2471737_mul x y) z;
  q2471737_mul_comm :
    forall x y : K,
      q2471737_mul x y = q2471737_mul y x;
  q2471737_mul_one :
    forall x : K,
      q2471737_mul x q2471737_one = x;
  q2471737_left_distrib :
    forall x y z : K,
      q2471737_mul x (q2471737_add y z) =
      q2471737_add
        (q2471737_mul x y) (q2471737_mul x z);
  q2471737_inv_zero :
    q2471737_inv q2471737_zero = q2471737_zero;
  q2471737_mul_inv :
    forall x : K,
      x <> q2471737_zero ->
      q2471737_mul x (q2471737_inv x) = q2471737_one;
  q2471737_le_refl :
    forall x : K,
      q2471737_le x x;
  q2471737_le_trans :
    forall x y z : K,
      q2471737_le x y ->
      q2471737_le y z ->
      q2471737_le x z;
  q2471737_le_antisym :
    forall x y : K,
      q2471737_le x y ->
      q2471737_le y x ->
      x = y;
  q2471737_le_total :
    forall x y : K,
      q2471737_le x y \/ q2471737_le y x;
  q2471737_add_le_add_left :
    forall x y z : K,
      q2471737_le x y ->
      q2471737_le
        (q2471737_add z x) (q2471737_add z y);
  q2471737_mul_nonnegative :
    forall x y : K,
      q2471737_le q2471737_zero x ->
      q2471737_le q2471737_zero y ->
      q2471737_le q2471737_zero (q2471737_mul x y)
}.

Arguments q2471737_zero {K} _.
Arguments q2471737_one {K} _.
Arguments q2471737_add {K} _ _ _.
Arguments q2471737_mul {K} _ _ _.
Arguments q2471737_neg {K} _ _.
Arguments q2471737_inv {K} _ _.
Arguments q2471737_le {K} _ _ _.

Record q2471737_module
    (K E : Type)
    (fld : q2471737_linear_ordered_field K) : Type := {
  q2471737_vzero : E;
  q2471737_vadd : E -> E -> E;
  q2471737_vneg : E -> E;
  q2471737_smul : K -> E -> E;
  q2471737_vadd_assoc :
    forall x y z : E,
      q2471737_vadd x (q2471737_vadd y z) =
      q2471737_vadd (q2471737_vadd x y) z;
  q2471737_vadd_comm :
    forall x y : E,
      q2471737_vadd x y = q2471737_vadd y x;
  q2471737_vadd_zero :
    forall x : E,
      q2471737_vadd x q2471737_vzero = x;
  q2471737_vadd_neg :
    forall x : E,
      q2471737_vadd x (q2471737_vneg x) = q2471737_vzero;
  q2471737_one_smul :
    forall x : E,
      q2471737_smul (q2471737_one fld) x = x;
  q2471737_mul_smul :
    forall (a b : K) (x : E),
      q2471737_smul (q2471737_mul fld a b) x =
      q2471737_smul a (q2471737_smul b x);
  q2471737_add_smul :
    forall (a b : K) (x : E),
      q2471737_smul (q2471737_add fld a b) x =
      q2471737_vadd
        (q2471737_smul a x) (q2471737_smul b x);
  q2471737_smul_add :
    forall (a : K) (x y : E),
      q2471737_smul a (q2471737_vadd x y) =
      q2471737_vadd
        (q2471737_smul a x) (q2471737_smul a y)
}.

Arguments q2471737_vzero {K E fld} _.
Arguments q2471737_vadd {K E fld} _ _ _.
Arguments q2471737_vneg {K E fld} _ _.
Arguments q2471737_smul {K E fld} _ _ _.

Definition q2471737_set (A : Type) : Type := A -> Prop.

Definition q2471737_subset {A : Type}
    (S T : q2471737_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q2471737_same_set {A : Type}
    (S T : q2471737_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q2471737_finite_set {A : Type}
    (S : q2471737_set A) : Prop :=
  exists enumeration : list A,
    NoDup enumeration /\
    forall x : A, S x <-> In x enumeration.

Fixpoint q2471737_scalar_sum
    {K I : Type}
    (fld : q2471737_linear_ordered_field K)
    (indices : list I)
    (weights : I -> K) : K :=
  match indices with
  | nil => q2471737_zero fld
  | cons i rest =>
      q2471737_add fld
        (weights i) (q2471737_scalar_sum fld rest weights)
  end.

Fixpoint q2471737_weighted_sum
    {K E I : Type}
    {fld : q2471737_linear_ordered_field K}
    (V : @q2471737_module K E fld)
    (indices : list I)
    (weights : I -> K)
    (points : I -> E) : E :=
  match indices with
  | nil => q2471737_vzero V
  | cons i rest =>
      q2471737_vadd V
        (q2471737_smul V (weights i) (points i))
        (q2471737_weighted_sum V rest weights points)
  end.

Definition q2471737_affine_independent_set
    {K E : Type}
    (fld : q2471737_linear_ordered_field K)
    (V : @q2471737_module K E fld)
    (S : q2471737_set E) : Prop :=
  forall (weights : E -> K) (support : list E),
    NoDup support ->
    (forall x : E,
      weights x <> q2471737_zero fld ->
      S x /\ In x support) ->
    q2471737_scalar_sum fld support weights =
      q2471737_zero fld ->
    q2471737_weighted_sum V support weights (fun x => x) =
      q2471737_vzero V ->
    forall x : E, S x -> weights x = q2471737_zero fld.

Definition q2471737_convex
    {K E : Type}
    (fld : q2471737_linear_ordered_field K)
    (V : @q2471737_module K E fld)
    (S : q2471737_set E) : Prop :=
  forall (x y : E) (a b : K),
    S x ->
    S y ->
    q2471737_le fld (q2471737_zero fld) a ->
    q2471737_le fld (q2471737_zero fld) b ->
    q2471737_add fld a b = q2471737_one fld ->
    S
      (q2471737_vadd V
        (q2471737_smul V a x)
        (q2471737_smul V b y)).

Definition q2471737_convex_hull
    {K E : Type}
    (fld : q2471737_linear_ordered_field K)
    (V : @q2471737_module K E fld)
    (S : q2471737_set E) : q2471737_set E :=
  fun x =>
    forall C : q2471737_set E,
      @q2471737_convex K E fld V C ->
      q2471737_subset S C ->
      C x.

Theorem convexHull_eq_union :
  forall (K E : Type)
         (fld : q2471737_linear_ordered_field K)
         (V : @q2471737_module K E fld)
         (S : q2471737_set E),
    q2471737_same_set
      (@q2471737_convex_hull K E fld V S)
      (fun x : E =>
        exists T : q2471737_set E,
          q2471737_finite_set T /\
          q2471737_subset T S /\
          @q2471737_affine_independent_set K E fld V T /\
          @q2471737_convex_hull K E fld V T x).
Admitted.
