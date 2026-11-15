(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1038716
  (thousand-theorems__rocq__Q1038716), "Identity theorem": two analytic
  functions on a preconnected subset of a nontrivially normed field that
  agree at distinct points arbitrarily close to a point of the subset agree
  throughout it.
  This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1038716_normed_field (K : Type) : Type := {
  q1038716_nf_zero : K;
  q1038716_nf_one : K;
  q1038716_nf_add : K -> K -> K;
  q1038716_nf_mul : K -> K -> K;
  q1038716_nf_neg : K -> K;
  q1038716_nf_inv : K -> K;
  q1038716_nf_add_assoc :
    forall x y z : K,
      q1038716_nf_add x (q1038716_nf_add y z) =
      q1038716_nf_add (q1038716_nf_add x y) z;
  q1038716_nf_add_comm :
    forall x y : K, q1038716_nf_add x y = q1038716_nf_add y x;
  q1038716_nf_add_zero :
    forall x : K, q1038716_nf_add x q1038716_nf_zero = x;
  q1038716_nf_add_neg :
    forall x : K, q1038716_nf_add x (q1038716_nf_neg x) =
      q1038716_nf_zero;
  q1038716_nf_mul_assoc :
    forall x y z : K,
      q1038716_nf_mul x (q1038716_nf_mul y z) =
      q1038716_nf_mul (q1038716_nf_mul x y) z;
  q1038716_nf_mul_comm :
    forall x y : K, q1038716_nf_mul x y = q1038716_nf_mul y x;
  q1038716_nf_mul_one :
    forall x : K, q1038716_nf_mul x q1038716_nf_one = x;
  q1038716_nf_left_distrib :
    forall x y z : K,
      q1038716_nf_mul x (q1038716_nf_add y z) =
      q1038716_nf_add
        (q1038716_nf_mul x y) (q1038716_nf_mul x z);
  q1038716_nf_inv_zero :
    q1038716_nf_inv q1038716_nf_zero = q1038716_nf_zero;
  q1038716_nf_mul_inv :
    forall x : K, x <> q1038716_nf_zero ->
      q1038716_nf_mul x (q1038716_nf_inv x) = q1038716_nf_one;
  q1038716_nf_nontrivial :
    q1038716_nf_zero <> q1038716_nf_one;
  q1038716_nf_norm : K -> R;
  q1038716_nf_norm_nonnegative :
    forall x : K, 0 <= q1038716_nf_norm x;
  q1038716_nf_norm_eq_zero :
    forall x : K,
      q1038716_nf_norm x = 0 <-> x = q1038716_nf_zero;
  q1038716_nf_norm_neg :
    forall x : K,
      q1038716_nf_norm (q1038716_nf_neg x) = q1038716_nf_norm x;
  q1038716_nf_norm_add_le :
    forall x y : K,
      q1038716_nf_norm (q1038716_nf_add x y) <=
      q1038716_nf_norm x + q1038716_nf_norm y;
  q1038716_nf_norm_mul :
    forall x y : K,
      q1038716_nf_norm (q1038716_nf_mul x y) =
      q1038716_nf_norm x * q1038716_nf_norm y;
  q1038716_nf_norm_nontrivial :
    exists x : K, 1 < q1038716_nf_norm x
}.

Arguments q1038716_nf_zero {K} _.
Arguments q1038716_nf_one {K} _.
Arguments q1038716_nf_add {K} _ _ _.
Arguments q1038716_nf_mul {K} _ _ _.
Arguments q1038716_nf_neg {K} _ _.
Arguments q1038716_nf_inv {K} _ _.
Arguments q1038716_nf_norm {K} _ _.

Record q1038716_normed_vector_space
    (K : Type) (F : q1038716_normed_field K) (E : Type) : Type := {
  q1038716_nv_zero : E;
  q1038716_nv_add : E -> E -> E;
  q1038716_nv_neg : E -> E;
  q1038716_nv_smul : K -> E -> E;
  q1038716_nv_norm : E -> R;
  q1038716_nv_add_assoc :
    forall x y z : E,
      q1038716_nv_add x (q1038716_nv_add y z) =
      q1038716_nv_add (q1038716_nv_add x y) z;
  q1038716_nv_add_comm :
    forall x y : E, q1038716_nv_add x y = q1038716_nv_add y x;
  q1038716_nv_add_zero :
    forall x : E, q1038716_nv_add x q1038716_nv_zero = x;
  q1038716_nv_add_neg :
    forall x : E, q1038716_nv_add x (q1038716_nv_neg x) =
      q1038716_nv_zero;
  q1038716_nv_one_smul :
    forall x : E,
      q1038716_nv_smul (q1038716_nf_one F) x = x;
  q1038716_nv_mul_smul :
    forall (a b : K) (x : E),
      q1038716_nv_smul (q1038716_nf_mul F a b) x =
      q1038716_nv_smul a (q1038716_nv_smul b x);
  q1038716_nv_add_smul :
    forall (a b : K) (x : E),
      q1038716_nv_smul (q1038716_nf_add F a b) x =
      q1038716_nv_add
        (q1038716_nv_smul a x) (q1038716_nv_smul b x);
  q1038716_nv_smul_add :
    forall (a : K) (x y : E),
      q1038716_nv_smul a (q1038716_nv_add x y) =
      q1038716_nv_add
        (q1038716_nv_smul a x) (q1038716_nv_smul a y);
  q1038716_nv_zero_smul :
    forall x : E,
      q1038716_nv_smul (q1038716_nf_zero F) x =
      q1038716_nv_zero;
  q1038716_nv_smul_zero :
    forall a : K, q1038716_nv_smul a q1038716_nv_zero =
      q1038716_nv_zero;
  q1038716_nv_norm_nonnegative :
    forall x : E, 0 <= q1038716_nv_norm x;
  q1038716_nv_norm_eq_zero :
    forall x : E,
      q1038716_nv_norm x = 0 <-> x = q1038716_nv_zero;
  q1038716_nv_norm_neg :
    forall x : E,
      q1038716_nv_norm (q1038716_nv_neg x) = q1038716_nv_norm x;
  q1038716_nv_norm_add_le :
    forall x y : E,
      q1038716_nv_norm (q1038716_nv_add x y) <=
      q1038716_nv_norm x + q1038716_nv_norm y;
  q1038716_nv_norm_smul :
    forall (a : K) (x : E),
      q1038716_nv_norm (q1038716_nv_smul a x) =
      q1038716_nf_norm F a * q1038716_nv_norm x
}.

Arguments q1038716_nv_zero {K F E} _.
Arguments q1038716_nv_add {K F E} _ _ _.
Arguments q1038716_nv_neg {K F E} _ _.
Arguments q1038716_nv_smul {K F E} _ _ _.
Arguments q1038716_nv_norm {K F E} _ _.

Definition q1038716_k_sub
    {K : Type} (F : q1038716_normed_field K) (x y : K) : K :=
  q1038716_nf_add F x (q1038716_nf_neg F y).

Definition q1038716_e_sub
    {K E : Type}
    {F : q1038716_normed_field K}
    (V : q1038716_normed_vector_space F E) (x y : E) : E :=
  q1038716_nv_add V x (q1038716_nv_neg V y).

Fixpoint q1038716_k_pow
    {K : Type} (F : q1038716_normed_field K)
    (x : K) (n : nat) : K :=
  match n with
  | O => q1038716_nf_one F
  | S m => q1038716_nf_mul F x (q1038716_k_pow F x m)
  end.

Fixpoint q1038716_partial_sum
    {K E : Type}
    {F : q1038716_normed_field K}
    (V : q1038716_normed_vector_space F E)
    (terms : nat -> E) (n : nat) : E :=
  match n with
  | O => q1038716_nv_zero V
  | S m =>
      q1038716_nv_add V
        (q1038716_partial_sum V terms m) (terms m)
  end.

Definition q1038716_converges
    {K E : Type}
    {F : q1038716_normed_field K}
    (V : q1038716_normed_vector_space F E)
    (sequence : nat -> E) (limit : E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      q1038716_nv_norm V
        (q1038716_e_sub V (sequence n) limit) < epsilon.

Definition q1038716_has_sum
    {K E : Type}
    {F : q1038716_normed_field K}
    (V : q1038716_normed_vector_space F E)
    (terms : nat -> E) (sum : E) : Prop :=
  q1038716_converges V
    (fun n => q1038716_partial_sum V terms n) sum.

Definition q1038716_analytic_at
    {K E : Type}
    (F : q1038716_normed_field K)
    (V : q1038716_normed_vector_space F E)
    (f : K -> E) (center : K) : Prop :=
  exists coefficients : nat -> E, exists radius : R,
    0 < radius /\
    forall z : K,
      q1038716_nf_norm F (q1038716_k_sub F z center) < radius ->
      q1038716_has_sum V
        (fun n : nat =>
          q1038716_nv_smul V
            (q1038716_k_pow F (q1038716_k_sub F z center) n)
            (coefficients n))
        (f z).

Definition q1038716_analytic_on_nhd
    {K E : Type}
    (F : q1038716_normed_field K)
    (V : q1038716_normed_vector_space F E)
    (f : K -> E) (U : K -> Prop) : Prop :=
  forall z : K, U z ->
    @q1038716_analytic_at K E F V f z.

Definition q1038716_metric_open
    {K : Type}
    (F : q1038716_normed_field K) (S : K -> Prop) : Prop :=
  forall x : K, S x ->
    exists radius : R, 0 < radius /\
      forall y : K,
        q1038716_nf_norm F (q1038716_k_sub F y x) < radius ->
        S y.

Definition q1038716_relatively_open
    {K : Type}
    (F : q1038716_normed_field K)
    (U S : K -> Prop) : Prop :=
  exists ambient : K -> Prop,
    q1038716_metric_open F ambient /\
    forall x : K, S x <-> U x /\ ambient x.

Definition q1038716_is_preconnected
    {K : Type}
    (F : q1038716_normed_field K) (U : K -> Prop) : Prop :=
  forall left right : K -> Prop,
    q1038716_relatively_open F U left ->
    q1038716_relatively_open F U right ->
    (forall x : K, U x <-> left x \/ right x) ->
    (forall x : K, ~ (left x /\ right x)) ->
    (forall x : K, ~ left x) \/ (forall x : K, ~ right x).

Definition q1038716_frequently_equal_near
    {K E : Type}
    (F : q1038716_normed_field K)
    (f g : K -> E) (center : K) : Prop :=
  forall radius : R, 0 < radius ->
    exists z : K,
      z <> center /\
      q1038716_nf_norm F (q1038716_k_sub F z center) < radius /\
      f z = g z.

Theorem AnalyticOnNhd_eqOn_of_preconnected_of_frequently_eq :
  forall (K E : Type)
         (F : q1038716_normed_field K)
         (V : q1038716_normed_vector_space F E)
         (U : K -> Prop) (f g : K -> E) (z0 : K),
    @q1038716_analytic_on_nhd K E F V f U ->
    @q1038716_analytic_on_nhd K E F V g U ->
    @q1038716_is_preconnected K F U ->
    U z0 ->
    @q1038716_frequently_equal_near K E F f g z0 ->
    forall z : K, U z -> f z = g z.
Admitted.
