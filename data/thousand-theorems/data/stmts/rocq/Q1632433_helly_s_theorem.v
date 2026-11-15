(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1632433
  (thousand-theorems__rocq__Q1632433), "Helly's theorem": for a finite family
  of convex sets in a finite-dimensional vector space over a linearly ordered
  field, if every subfamily of dimension plus one has nonempty intersection,
  then the whole family has nonempty intersection. This file contains no proof.
*)

From Stdlib Require Import Arith List Vectors.Fin.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1632433_linear_ordered_field (K : Type) : Type := {
  q1632433_zero : K;
  q1632433_one : K;
  q1632433_add : K -> K -> K;
  q1632433_mul : K -> K -> K;
  q1632433_neg : K -> K;
  q1632433_inv : K -> K;
  q1632433_le : K -> K -> Prop;
  q1632433_zero_ne_one :
    q1632433_zero <> q1632433_one;
  q1632433_add_assoc :
    forall x y z : K,
      q1632433_add x (q1632433_add y z) =
      q1632433_add (q1632433_add x y) z;
  q1632433_add_comm :
    forall x y : K,
      q1632433_add x y = q1632433_add y x;
  q1632433_add_zero :
    forall x : K,
      q1632433_add x q1632433_zero = x;
  q1632433_add_neg :
    forall x : K,
      q1632433_add x (q1632433_neg x) = q1632433_zero;
  q1632433_mul_assoc :
    forall x y z : K,
      q1632433_mul x (q1632433_mul y z) =
      q1632433_mul (q1632433_mul x y) z;
  q1632433_mul_comm :
    forall x y : K,
      q1632433_mul x y = q1632433_mul y x;
  q1632433_mul_one :
    forall x : K,
      q1632433_mul x q1632433_one = x;
  q1632433_left_distrib :
    forall x y z : K,
      q1632433_mul x (q1632433_add y z) =
      q1632433_add
        (q1632433_mul x y) (q1632433_mul x z);
  q1632433_inv_zero :
    q1632433_inv q1632433_zero = q1632433_zero;
  q1632433_mul_inv :
    forall x : K,
      x <> q1632433_zero ->
      q1632433_mul x (q1632433_inv x) = q1632433_one;
  q1632433_le_refl :
    forall x : K,
      q1632433_le x x;
  q1632433_le_trans :
    forall x y z : K,
      q1632433_le x y ->
      q1632433_le y z ->
      q1632433_le x z;
  q1632433_le_antisym :
    forall x y : K,
      q1632433_le x y ->
      q1632433_le y x ->
      x = y;
  q1632433_le_total :
    forall x y : K,
      q1632433_le x y \/ q1632433_le y x;
  q1632433_add_le_add_left :
    forall x y z : K,
      q1632433_le x y ->
      q1632433_le
        (q1632433_add z x) (q1632433_add z y);
  q1632433_mul_nonnegative :
    forall x y : K,
      q1632433_le q1632433_zero x ->
      q1632433_le q1632433_zero y ->
      q1632433_le q1632433_zero (q1632433_mul x y)
}.

Arguments q1632433_zero {K} _.
Arguments q1632433_one {K} _.
Arguments q1632433_add {K} _ _ _.
Arguments q1632433_mul {K} _ _ _.
Arguments q1632433_neg {K} _ _.
Arguments q1632433_inv {K} _ _.
Arguments q1632433_le {K} _ _ _.

Record q1632433_module
    (K E : Type)
    (fld : q1632433_linear_ordered_field K) : Type := {
  q1632433_vzero : E;
  q1632433_vadd : E -> E -> E;
  q1632433_vneg : E -> E;
  q1632433_smul : K -> E -> E;
  q1632433_vadd_assoc :
    forall x y z : E,
      q1632433_vadd x (q1632433_vadd y z) =
      q1632433_vadd (q1632433_vadd x y) z;
  q1632433_vadd_comm :
    forall x y : E,
      q1632433_vadd x y = q1632433_vadd y x;
  q1632433_vadd_zero :
    forall x : E,
      q1632433_vadd x q1632433_vzero = x;
  q1632433_vadd_neg :
    forall x : E,
      q1632433_vadd x (q1632433_vneg x) = q1632433_vzero;
  q1632433_one_smul :
    forall x : E,
      q1632433_smul (q1632433_one fld) x = x;
  q1632433_mul_smul :
    forall (a b : K) (x : E),
      q1632433_smul (q1632433_mul fld a b) x =
      q1632433_smul a (q1632433_smul b x);
  q1632433_add_smul :
    forall (a b : K) (x : E),
      q1632433_smul (q1632433_add fld a b) x =
      q1632433_vadd
        (q1632433_smul a x) (q1632433_smul b x);
  q1632433_smul_add :
    forall (a : K) (x y : E),
      q1632433_smul a (q1632433_vadd x y) =
      q1632433_vadd
        (q1632433_smul a x) (q1632433_smul a y)
}.

Arguments q1632433_vzero {K E fld} _.
Arguments q1632433_vadd {K E fld} _ _ _.
Arguments q1632433_vneg {K E fld} _ _.
Arguments q1632433_smul {K E fld} _ _ _.

Fixpoint q1632433_vector_sum
    {K E : Type}
    {fld : q1632433_linear_ordered_field K}
    (V : @q1632433_module K E fld)
    (n : nat) : (Fin.t n -> E) -> E :=
  match n as m return (Fin.t m -> E) -> E with
  | O =>
      fun _ => q1632433_vzero V
  | S m =>
      fun terms =>
        q1632433_vadd V
          (terms Fin.F1)
          (@q1632433_vector_sum K E fld V m
            (fun i => terms (Fin.FS i)))
  end.

Arguments q1632433_vector_sum {K E fld} V n _.

Definition q1632433_is_basis
    {K E : Type}
    {fld : q1632433_linear_ordered_field K}
    (V : @q1632433_module K E fld)
    (d : nat)
    (basis : Fin.t d -> E) : Prop :=
  (forall x : E,
    exists coefficients : Fin.t d -> K,
      x =
        q1632433_vector_sum V d
          (fun i =>
            q1632433_smul V
              (coefficients i) (basis i))) /\
  forall coefficients : Fin.t d -> K,
    q1632433_vector_sum V d
      (fun i =>
        q1632433_smul V
          (coefficients i) (basis i)) =
      q1632433_vzero V ->
    forall i : Fin.t d,
      coefficients i = q1632433_zero fld.

Definition q1632433_has_finrank
    {K E : Type}
    {fld : q1632433_linear_ordered_field K}
    (V : @q1632433_module K E fld)
    (d : nat) : Prop :=
  exists basis : Fin.t d -> E,
    @q1632433_is_basis K E fld V d basis.

Arguments q1632433_is_basis {K E fld} V d basis.
Arguments q1632433_has_finrank {K E fld} V d.

Definition q1632433_set (A : Type) : Type :=
  A -> Prop.

Definition q1632433_convex
    {K E : Type}
    {fld : q1632433_linear_ordered_field K}
    (V : @q1632433_module K E fld)
    (S : q1632433_set E) : Prop :=
  forall (x y : E) (a b : K),
    S x ->
    S y ->
    q1632433_le fld (q1632433_zero fld) a ->
    q1632433_le fld (q1632433_zero fld) b ->
    q1632433_add fld a b = q1632433_one fld ->
    S
      (q1632433_vadd V
        (q1632433_smul V a x)
        (q1632433_smul V b y)).

Theorem q1632433_helly_theorem :
  forall (K E I : Type)
         (fld : q1632433_linear_ordered_field K)
         (V : @q1632433_module K E fld)
         (d : nat)
         (F : I -> q1632433_set E)
         (family : list I),
    q1632433_has_finrank V d ->
    NoDup family ->
    (S d <= length family)%nat ->
    (forall i : I,
      In i family ->
      q1632433_convex V (F i)) ->
    (forall subfamily : list I,
      NoDup subfamily ->
      (forall i : I, In i subfamily -> In i family) ->
      length subfamily = S d ->
      exists x : E,
        forall i : I, In i subfamily -> F i x) ->
    exists x : E,
      forall i : I, In i family -> F i x.
Admitted.
