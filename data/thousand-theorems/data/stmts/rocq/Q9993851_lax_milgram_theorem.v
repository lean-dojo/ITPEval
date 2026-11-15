(*
  Statement-only formalization of Thousand Theorems corpus artifact Q9993851
  (thousand-theorems__rocq__Q9993851), "Lax–Milgram theorem": every bounded
  coercive bilinear form on a complete real inner-product space is represented
  by a continuous linear self-equivalence. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q9993851_real_inner_product_space (V : Type) : Type := {
  q9993851_zero : V;
  q9993851_add : V -> V -> V;
  q9993851_neg : V -> V;
  q9993851_smul : R -> V -> V;
  q9993851_inner : V -> V -> R;

  q9993851_add_assoc :
    forall x y z : V,
      q9993851_add x (q9993851_add y z) =
      q9993851_add (q9993851_add x y) z;
  q9993851_add_comm :
    forall x y : V, q9993851_add x y = q9993851_add y x;
  q9993851_add_zero :
    forall x : V, q9993851_add x q9993851_zero = x;
  q9993851_add_neg :
    forall x : V,
      q9993851_add x (q9993851_neg x) = q9993851_zero;

  q9993851_one_smul :
    forall x : V, q9993851_smul 1 x = x;
  q9993851_mul_smul :
    forall (a b : R) (x : V),
      q9993851_smul (a * b) x =
      q9993851_smul a (q9993851_smul b x);
  q9993851_add_smul :
    forall (a b : R) (x : V),
      q9993851_smul (a + b) x =
      q9993851_add
        (q9993851_smul a x) (q9993851_smul b x);
  q9993851_smul_add :
    forall (a : R) (x y : V),
      q9993851_smul a (q9993851_add x y) =
      q9993851_add
        (q9993851_smul a x) (q9993851_smul a y);
  q9993851_zero_smul :
    forall x : V, q9993851_smul 0 x = q9993851_zero;
  q9993851_smul_zero :
    forall a : R, q9993851_smul a q9993851_zero = q9993851_zero;

  q9993851_inner_add_left :
    forall x y z : V,
      q9993851_inner (q9993851_add x y) z =
      q9993851_inner x z + q9993851_inner y z;
  q9993851_inner_smul_left :
    forall (a : R) (x y : V),
      q9993851_inner (q9993851_smul a x) y =
      a * q9993851_inner x y;
  q9993851_inner_symm :
    forall x y : V, q9993851_inner x y = q9993851_inner y x;
  q9993851_inner_nonnegative :
    forall x : V, 0 <= q9993851_inner x x;
  q9993851_inner_eq_zero :
    forall x : V,
      q9993851_inner x x = 0 <-> x = q9993851_zero
}.

Arguments q9993851_zero {V} _.
Arguments q9993851_add {V} _ _ _.
Arguments q9993851_neg {V} _ _.
Arguments q9993851_smul {V} _ _ _.
Arguments q9993851_inner {V} _ _ _.

Definition q9993851_sub
    {V : Type}
    (H : q9993851_real_inner_product_space V)
    (x y : V) : V :=
  q9993851_add H x (q9993851_neg H y).

Definition q9993851_norm
    {V : Type}
    (H : q9993851_real_inner_product_space V)
    (x : V) : R :=
  sqrt (q9993851_inner H x x).

Definition q9993851_sequence_converges
    {V : Type}
    (H : q9993851_real_inner_product_space V)
    (u : nat -> V) (limit : V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q9993851_norm H
          (q9993851_sub H (u n) limit) < epsilon.

Definition q9993851_sequence_cauchy
    {V : Type}
    (H : q9993851_real_inner_product_space V)
    (u : nat -> V) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q9993851_norm H
          (q9993851_sub H (u m) (u n)) < epsilon.

Definition q9993851_complete
    {V : Type}
    (H : q9993851_real_inner_product_space V) : Prop :=
  forall u : nat -> V,
    q9993851_sequence_cauchy H u ->
    exists limit : V,
      q9993851_sequence_converges H u limit.

Record q9993851_continuous_linear_map
    (V : Type)
    (H : q9993851_real_inner_product_space V) : Type := {
  q9993851_clm_fun : V -> V;
  q9993851_clm_add :
    forall x y : V,
      q9993851_clm_fun (q9993851_add H x y) =
      q9993851_add H
        (q9993851_clm_fun x) (q9993851_clm_fun y);
  q9993851_clm_smul :
    forall (a : R) (x : V),
      q9993851_clm_fun (q9993851_smul H a x) =
      q9993851_smul H a (q9993851_clm_fun x);
  q9993851_clm_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : V,
        q9993851_norm H (q9993851_clm_fun x) <=
        bound * q9993851_norm H x
}.

Arguments q9993851_clm_fun {V H} _ _.

Record q9993851_continuous_linear_equiv
    (V : Type)
    (H : q9993851_real_inner_product_space V) : Type := {
  q9993851_cle_forward :
    q9993851_continuous_linear_map H;
  q9993851_cle_inverse :
    q9993851_continuous_linear_map H;
  q9993851_cle_left_inverse :
    forall x : V,
      q9993851_clm_fun q9993851_cle_inverse
        (q9993851_clm_fun q9993851_cle_forward x) = x;
  q9993851_cle_right_inverse :
    forall y : V,
      q9993851_clm_fun q9993851_cle_forward
        (q9993851_clm_fun q9993851_cle_inverse y) = y
}.

Arguments q9993851_cle_forward {V H} _.
Arguments q9993851_cle_inverse {V H} _.

Definition q9993851_bounded_bilinear_form
    {V : Type}
    (H : q9993851_real_inner_product_space V)
    (B : V -> V -> R) : Prop :=
  (forall x y z : V,
    B (q9993851_add H x y) z = B x z + B y z) /\
  (forall (a : R) (x y : V),
    B (q9993851_smul H a x) y = a * B x y) /\
  (forall x y z : V,
    B x (q9993851_add H y z) = B x y + B x z) /\
  (forall (a : R) (x y : V),
    B x (q9993851_smul H a y) = a * B x y) /\
  exists bound : R,
    0 <= bound /\
    forall x y : V,
      Rabs (B x y) <=
      bound * q9993851_norm H x * q9993851_norm H y.

Definition q9993851_is_coercive
    {V : Type}
    (H : q9993851_real_inner_product_space V)
    (B : V -> V -> R) : Prop :=
  exists coercivity_constant : R,
    0 < coercivity_constant /\
    forall u : V,
      coercivity_constant * q9993851_norm H u * q9993851_norm H u
      <= B u u.

Theorem IsCoercive_continuousLinearEquivOfBilin :
  forall (V : Type)
         (H : q9993851_real_inner_product_space V),
    q9993851_complete H ->
    forall B : V -> V -> R,
      q9993851_bounded_bilinear_form H B ->
      q9993851_is_coercive H B ->
      exists equivalence : q9993851_continuous_linear_equiv H,
        forall v w : V,
          q9993851_inner H
            (q9993851_clm_fun
              (q9993851_cle_forward equivalence) v) w =
          B v w.
Admitted.
