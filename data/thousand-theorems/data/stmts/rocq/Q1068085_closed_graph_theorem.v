(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1068085
  (thousand-theorems__rocq__Q1068085), "Closed graph theorem": a linear map
  between Banach spaces over a nontrivially normed field is continuous when
  its graph is closed. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1068085_normed_field (K : Type) : Type := {
  q1068085_nf_zero : K;
  q1068085_nf_one : K;
  q1068085_nf_add : K -> K -> K;
  q1068085_nf_mul : K -> K -> K;
  q1068085_nf_neg : K -> K;
  q1068085_nf_inv : K -> K;
  q1068085_nf_add_assoc :
    forall x y z : K,
      q1068085_nf_add x (q1068085_nf_add y z) =
      q1068085_nf_add (q1068085_nf_add x y) z;
  q1068085_nf_add_comm :
    forall x y : K, q1068085_nf_add x y = q1068085_nf_add y x;
  q1068085_nf_add_zero :
    forall x : K, q1068085_nf_add x q1068085_nf_zero = x;
  q1068085_nf_add_neg :
    forall x : K,
      q1068085_nf_add x (q1068085_nf_neg x) = q1068085_nf_zero;
  q1068085_nf_mul_assoc :
    forall x y z : K,
      q1068085_nf_mul x (q1068085_nf_mul y z) =
      q1068085_nf_mul (q1068085_nf_mul x y) z;
  q1068085_nf_mul_comm :
    forall x y : K, q1068085_nf_mul x y = q1068085_nf_mul y x;
  q1068085_nf_mul_one :
    forall x : K, q1068085_nf_mul x q1068085_nf_one = x;
  q1068085_nf_left_distrib :
    forall x y z : K,
      q1068085_nf_mul x (q1068085_nf_add y z) =
      q1068085_nf_add
        (q1068085_nf_mul x y) (q1068085_nf_mul x z);
  q1068085_nf_inv_zero :
    q1068085_nf_inv q1068085_nf_zero = q1068085_nf_zero;
  q1068085_nf_mul_inv :
    forall x : K, x <> q1068085_nf_zero ->
      q1068085_nf_mul x (q1068085_nf_inv x) = q1068085_nf_one;
  q1068085_nf_nontrivial :
    q1068085_nf_zero <> q1068085_nf_one;
  q1068085_nf_norm : K -> R;
  q1068085_nf_norm_nonnegative :
    forall x : K, 0 <= q1068085_nf_norm x;
  q1068085_nf_norm_eq_zero :
    forall x : K,
      q1068085_nf_norm x = 0 <-> x = q1068085_nf_zero;
  q1068085_nf_norm_neg :
    forall x : K,
      q1068085_nf_norm (q1068085_nf_neg x) = q1068085_nf_norm x;
  q1068085_nf_norm_add_le :
    forall x y : K,
      q1068085_nf_norm (q1068085_nf_add x y) <=
      q1068085_nf_norm x + q1068085_nf_norm y;
  q1068085_nf_norm_mul :
    forall x y : K,
      q1068085_nf_norm (q1068085_nf_mul x y) =
      q1068085_nf_norm x * q1068085_nf_norm y;
  q1068085_nf_norm_nontrivial :
    exists x : K, 1 < q1068085_nf_norm x
}.

Arguments q1068085_nf_zero {K} _.
Arguments q1068085_nf_one {K} _.
Arguments q1068085_nf_add {K} _ _ _.
Arguments q1068085_nf_mul {K} _ _ _.
Arguments q1068085_nf_neg {K} _ _.
Arguments q1068085_nf_inv {K} _ _.
Arguments q1068085_nf_norm {K} _ _.

Record q1068085_normed_vector_space
    (K : Type) (F : q1068085_normed_field K) (E : Type) : Type := {
  q1068085_nv_zero : E;
  q1068085_nv_add : E -> E -> E;
  q1068085_nv_neg : E -> E;
  q1068085_nv_smul : K -> E -> E;
  q1068085_nv_norm : E -> R;
  q1068085_nv_add_assoc :
    forall x y z : E,
      q1068085_nv_add x (q1068085_nv_add y z) =
      q1068085_nv_add (q1068085_nv_add x y) z;
  q1068085_nv_add_comm :
    forall x y : E, q1068085_nv_add x y = q1068085_nv_add y x;
  q1068085_nv_add_zero :
    forall x : E, q1068085_nv_add x q1068085_nv_zero = x;
  q1068085_nv_add_neg :
    forall x : E,
      q1068085_nv_add x (q1068085_nv_neg x) = q1068085_nv_zero;
  q1068085_nv_one_smul :
    forall x : E,
      q1068085_nv_smul (q1068085_nf_one F) x = x;
  q1068085_nv_mul_smul :
    forall (a b : K) (x : E),
      q1068085_nv_smul (q1068085_nf_mul F a b) x =
      q1068085_nv_smul a (q1068085_nv_smul b x);
  q1068085_nv_add_smul :
    forall (a b : K) (x : E),
      q1068085_nv_smul (q1068085_nf_add F a b) x =
      q1068085_nv_add
        (q1068085_nv_smul a x) (q1068085_nv_smul b x);
  q1068085_nv_smul_add :
    forall (a : K) (x y : E),
      q1068085_nv_smul a (q1068085_nv_add x y) =
      q1068085_nv_add
        (q1068085_nv_smul a x) (q1068085_nv_smul a y);
  q1068085_nv_zero_smul :
    forall x : E,
      q1068085_nv_smul (q1068085_nf_zero F) x = q1068085_nv_zero;
  q1068085_nv_smul_zero :
    forall a : K,
      q1068085_nv_smul a q1068085_nv_zero = q1068085_nv_zero;
  q1068085_nv_norm_nonnegative :
    forall x : E, 0 <= q1068085_nv_norm x;
  q1068085_nv_norm_eq_zero :
    forall x : E,
      q1068085_nv_norm x = 0 <-> x = q1068085_nv_zero;
  q1068085_nv_norm_neg :
    forall x : E,
      q1068085_nv_norm (q1068085_nv_neg x) = q1068085_nv_norm x;
  q1068085_nv_norm_add_le :
    forall x y : E,
      q1068085_nv_norm (q1068085_nv_add x y) <=
      q1068085_nv_norm x + q1068085_nv_norm y;
  q1068085_nv_norm_smul :
    forall (a : K) (x : E),
      q1068085_nv_norm (q1068085_nv_smul a x) =
      q1068085_nf_norm F a * q1068085_nv_norm x
}.

Arguments q1068085_nv_zero {K F E} _.
Arguments q1068085_nv_add {K F E} _ _ _.
Arguments q1068085_nv_neg {K F E} _ _.
Arguments q1068085_nv_smul {K F E} _ _ _.
Arguments q1068085_nv_norm {K F E} _ _.

Definition q1068085_sub
    {K E : Type}
    {F : q1068085_normed_field K}
    (V : q1068085_normed_vector_space F E)
    (x y : E) : E :=
  q1068085_nv_add V x (q1068085_nv_neg V y).

Definition q1068085_dist
    {K E : Type}
    {F : q1068085_normed_field K}
    (V : q1068085_normed_vector_space F E)
    (x y : E) : R :=
  q1068085_nv_norm V (q1068085_sub V x y).

Definition q1068085_sequence_converges
    {K E : Type}
    {F : q1068085_normed_field K}
    (V : q1068085_normed_vector_space F E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      q1068085_dist V (u n) limit < epsilon.

Definition q1068085_sequence_cauchy
    {K E : Type}
    {F : q1068085_normed_field K}
    (V : q1068085_normed_vector_space F E)
    (u : nat -> E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat ->
      (N <= n)%nat ->
      q1068085_dist V (u m) (u n) < epsilon.

Definition q1068085_complete
    {K E : Type}
    {F : q1068085_normed_field K}
    (V : q1068085_normed_vector_space F E) : Prop :=
  forall u : nat -> E,
    q1068085_sequence_cauchy V u ->
    exists limit : E, q1068085_sequence_converges V u limit.

Record q1068085_linear_map
    {K E G : Type}
    {F : q1068085_normed_field K}
    (VE : q1068085_normed_vector_space F E)
    (VG : q1068085_normed_vector_space F G)
    (f : E -> G) : Prop := {
  q1068085_linear_map_add :
    forall x y : E,
      f (q1068085_nv_add VE x y) =
      q1068085_nv_add VG (f x) (f y);
  q1068085_linear_map_smul :
    forall (a : K) (x : E),
      f (q1068085_nv_smul VE a x) =
      q1068085_nv_smul VG a (f x)
}.

Definition q1068085_product_dist
    {K E G : Type}
    {F : q1068085_normed_field K}
    (VE : q1068085_normed_vector_space F E)
    (VG : q1068085_normed_vector_space F G)
    (p q : E * G) : R :=
  Rmax
    (q1068085_dist VE (fst p) (fst q))
    (q1068085_dist VG (snd p) (snd q)).

Definition q1068085_metric_open
    {X : Type}
    (distance : X -> X -> R)
    (U : X -> Prop) : Prop :=
  forall x : X, U x ->
    exists radius : R, 0 < radius /\
      forall y : X, distance y x < radius -> U y.

Definition q1068085_metric_closed
    {X : Type}
    (distance : X -> X -> R)
    (S : X -> Prop) : Prop :=
  q1068085_metric_open distance (fun x : X => ~ S x).

Definition q1068085_graph
    {E G : Type} (f : E -> G) : E * G -> Prop :=
  fun p : E * G => snd p = f (fst p).

Definition q1068085_closed_graph
    {K E G : Type}
    {F : q1068085_normed_field K}
    (VE : q1068085_normed_vector_space F E)
    (VG : q1068085_normed_vector_space F G)
    (f : E -> G) : Prop :=
  q1068085_metric_closed
    (q1068085_product_dist VE VG)
    (q1068085_graph f).

Definition q1068085_continuous
    {K E G : Type}
    {F : q1068085_normed_field K}
    (VE : q1068085_normed_vector_space F E)
    (VG : q1068085_normed_vector_space F G)
    (f : E -> G) : Prop :=
  forall x : E, forall epsilon : R, 0 < epsilon ->
    exists delta : R, 0 < delta /\
      forall y : E,
        q1068085_dist VE y x < delta ->
        q1068085_dist VG (f y) (f x) < epsilon.

Theorem LinearMap_continuous_of_isClosed_graph :
  forall (K E G : Type)
         (F : q1068085_normed_field K)
         (VE : q1068085_normed_vector_space F E)
         (VG : q1068085_normed_vector_space F G)
         (g : E -> G),
    q1068085_linear_map VE VG g ->
    q1068085_complete VE ->
    q1068085_complete VG ->
    q1068085_closed_graph VE VG g ->
    q1068085_continuous VE VG g.
Admitted.
