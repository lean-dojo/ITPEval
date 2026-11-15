(*
  Statement-only formalization of Thousand Theorems corpus artifact Q931001
  (thousand-theorems__rocq__Q931001), "Inverse function theorem": a map from a
  complete normed space over an arbitrary nontrivially normed field, with an
  invertible strict Frechet derivative at a point, has a local inverse whose
  strict derivative is the inverse continuous linear map. This file contains
  no proof.
*)

From Stdlib Require Import Reals Arith ClassicalEpsilon.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q931001_nontrivially_normed_field (K : Type) : Type := {
  q931001_zeroK : K;
  q931001_oneK : K;
  q931001_addK : K -> K -> K;
  q931001_mulK : K -> K -> K;
  q931001_negK : K -> K;
  q931001_invK : K -> K;
  q931001_normK : K -> R;
  q931001_zero_neq_oneK :
    q931001_zeroK <> q931001_oneK;
  q931001_addK_assoc :
    forall a b c : K,
      q931001_addK a (q931001_addK b c) =
      q931001_addK (q931001_addK a b) c;
  q931001_addK_comm :
    forall a b : K,
      q931001_addK a b = q931001_addK b a;
  q931001_addK_zero :
    forall a : K,
      q931001_addK a q931001_zeroK = a;
  q931001_addK_neg :
    forall a : K,
      q931001_addK a (q931001_negK a) = q931001_zeroK;
  q931001_mulK_assoc :
    forall a b c : K,
      q931001_mulK a (q931001_mulK b c) =
      q931001_mulK (q931001_mulK a b) c;
  q931001_mulK_comm :
    forall a b : K,
      q931001_mulK a b = q931001_mulK b a;
  q931001_mulK_one :
    forall a : K,
      q931001_mulK a q931001_oneK = a;
  q931001_mulK_add :
    forall a b c : K,
      q931001_mulK a (q931001_addK b c) =
      q931001_addK
        (q931001_mulK a b) (q931001_mulK a c);
  q931001_invK_zero :
    q931001_invK q931001_zeroK = q931001_zeroK;
  q931001_mulK_inv :
    forall a : K,
      a <> q931001_zeroK ->
      q931001_mulK a (q931001_invK a) = q931001_oneK;
  q931001_normK_nonnegative :
    forall a : K,
      0 <= q931001_normK a;
  q931001_normK_eq_zero :
    forall a : K,
      q931001_normK a = 0 <-> a = q931001_zeroK;
  q931001_normK_neg :
    forall a : K,
      q931001_normK (q931001_negK a) = q931001_normK a;
  q931001_normK_add_le :
    forall a b : K,
      q931001_normK (q931001_addK a b) <=
      q931001_normK a + q931001_normK b;
  q931001_normK_mul :
    forall a b : K,
      q931001_normK (q931001_mulK a b) =
      q931001_normK a * q931001_normK b;
  q931001_normK_nontrivial :
    exists a : K, 1 < q931001_normK a
}.

Arguments q931001_zeroK {K} _.
Arguments q931001_oneK {K} _.
Arguments q931001_addK {K} _ _ _.
Arguments q931001_mulK {K} _ _ _.
Arguments q931001_negK {K} _ _.
Arguments q931001_invK {K} _ _.
Arguments q931001_normK {K} _ _.

Record q931001_normed_space
    (K E : Type)
    (KF : q931001_nontrivially_normed_field K) : Type := {
  q931001_zeroV : E;
  q931001_addV : E -> E -> E;
  q931001_negV : E -> E;
  q931001_smulV : K -> E -> E;
  q931001_normV : E -> R;
  q931001_addV_assoc :
    forall x y z : E,
      q931001_addV x (q931001_addV y z) =
      q931001_addV (q931001_addV x y) z;
  q931001_addV_comm :
    forall x y : E,
      q931001_addV x y = q931001_addV y x;
  q931001_addV_zero :
    forall x : E,
      q931001_addV x q931001_zeroV = x;
  q931001_addV_neg :
    forall x : E,
      q931001_addV x (q931001_negV x) = q931001_zeroV;
  q931001_one_smul :
    forall x : E,
      q931001_smulV (q931001_oneK KF) x = x;
  q931001_mul_smul :
    forall (a b : K) (x : E),
      q931001_smulV (q931001_mulK KF a b) x =
      q931001_smulV a (q931001_smulV b x);
  q931001_add_smul :
    forall (a b : K) (x : E),
      q931001_smulV (q931001_addK KF a b) x =
      q931001_addV
        (q931001_smulV a x) (q931001_smulV b x);
  q931001_smul_add :
    forall (a : K) (x y : E),
      q931001_smulV a (q931001_addV x y) =
      q931001_addV
        (q931001_smulV a x) (q931001_smulV a y);
  q931001_zero_smul :
    forall x : E,
      q931001_smulV (q931001_zeroK KF) x = q931001_zeroV;
  q931001_smul_zero :
    forall a : K,
      q931001_smulV a q931001_zeroV = q931001_zeroV;
  q931001_normV_nonnegative :
    forall x : E,
      0 <= q931001_normV x;
  q931001_normV_eq_zero :
    forall x : E,
      q931001_normV x = 0 <-> x = q931001_zeroV;
  q931001_normV_neg :
    forall x : E,
      q931001_normV (q931001_negV x) = q931001_normV x;
  q931001_normV_add_le :
    forall x y : E,
      q931001_normV (q931001_addV x y) <=
      q931001_normV x + q931001_normV y;
  q931001_normV_smul :
    forall (a : K) (x : E),
      q931001_normV (q931001_smulV a x) =
      q931001_normK KF a * q931001_normV x
}.

Arguments q931001_zeroV {K E KF} _.
Arguments q931001_addV {K E KF} _ _ _.
Arguments q931001_negV {K E KF} _ _.
Arguments q931001_smulV {K E KF} _ _ _.
Arguments q931001_normV {K E KF} _ _.

Definition q931001_sub
    {K E : Type}
    {KF : q931001_nontrivially_normed_field K}
    (V : @q931001_normed_space K E KF)
    (x y : E) : E :=
  q931001_addV V x (q931001_negV V y).

Definition q931001_sequence_cauchy
    {K E : Type}
    {KF : q931001_nontrivially_normed_field K}
    (V : @q931001_normed_space K E KF)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q931001_normV V
          (q931001_sub V (u m) (u n)) < epsilon.

Definition q931001_sequence_converges
    {K E : Type}
    {KF : q931001_nontrivially_normed_field K}
    (V : @q931001_normed_space K E KF)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q931001_normV V
          (q931001_sub V (u n) limit) < epsilon.

Definition q931001_complete
    {K E : Type}
    {KF : q931001_nontrivially_normed_field K}
    (V : @q931001_normed_space K E KF) : Prop :=
  forall u : nat -> E,
    q931001_sequence_cauchy V u ->
    exists limit : E,
      q931001_sequence_converges V u limit.

Record q931001_continuous_linear_map
    (K E F : Type)
    (KF : q931001_nontrivially_normed_field K)
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF) : Type := {
  q931001_clm_fun : E -> F;
  q931001_clm_add :
    forall x y : E,
      q931001_clm_fun (q931001_addV VE x y) =
      q931001_addV VF
        (q931001_clm_fun x) (q931001_clm_fun y);
  q931001_clm_smul :
    forall (a : K) (x : E),
      q931001_clm_fun (q931001_smulV VE a x) =
      q931001_smulV VF a (q931001_clm_fun x);
  q931001_clm_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : E,
        q931001_normV VF (q931001_clm_fun x) <=
        bound * q931001_normV VE x
}.

Arguments q931001_clm_fun {K E F KF VE VF} _ _.

Record q931001_continuous_linear_equiv
    (K E F : Type)
    (KF : q931001_nontrivially_normed_field K)
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF) : Type := {
  q931001_cle_forward :
    @q931001_continuous_linear_map K E F KF VE VF;
  q931001_cle_inverse :
    @q931001_continuous_linear_map K F E KF VF VE;
  q931001_cle_left_inverse :
    forall x : E,
      q931001_clm_fun q931001_cle_inverse
        (q931001_clm_fun q931001_cle_forward x) = x;
  q931001_cle_right_inverse :
    forall y : F,
      q931001_clm_fun q931001_cle_forward
        (q931001_clm_fun q931001_cle_inverse y) = y
}.

Arguments q931001_cle_forward {K E F KF VE VF} _.
Arguments q931001_cle_inverse {K E F KF VE VF} _.

Definition q931001_has_strict_fderiv_at
    {K E F : Type}
    {KF : q931001_nontrivially_normed_field K}
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF)
    (f : E -> F)
    (derivative :
      @q931001_continuous_linear_map K E F KF VE VF)
    (point : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall x y : E,
        q931001_normV VE (q931001_sub VE x point) < delta ->
        q931001_normV VE (q931001_sub VE y point) < delta ->
        q931001_normV VF
          (q931001_sub VF
            (q931001_sub VF (f x) (f y))
            (q931001_clm_fun derivative
              (q931001_sub VE x y))) <=
        epsilon * q931001_normV VE (q931001_sub VE x y).

Definition q931001_continuous_at
    {K E F : Type}
    {KF : q931001_nontrivially_normed_field K}
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF)
    (g : F -> E) (source_point : F) (target_point : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : F,
        q931001_normV VF
          (q931001_sub VF y source_point) < delta ->
        q931001_normV VE
          (q931001_sub VE (g y) target_point) < epsilon.

Definition q931001_is_local_inverse_at
    {K E F : Type}
    {KF : q931001_nontrivially_normed_field K}
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF)
    (f : E -> F) (g : F -> E) (point : E) : Prop :=
  exists source_radius target_radius : R,
    0 < source_radius /\
    0 < target_radius /\
    (forall x : E,
      q931001_normV VE
        (q931001_sub VE x point) < source_radius ->
      g (f x) = x) /\
    (forall y : F,
      q931001_normV VF
        (q931001_sub VF y (f point)) < target_radius ->
      f (g y) = y) /\
    @q931001_continuous_at
      K E F KF VE VF g (f point) point.

Definition q931001_local_inverse
    {K E F : Type}
    {KF : q931001_nontrivially_normed_field K}
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF)
    (f : E -> F) (point : E) : F -> E :=
  epsilon
    (inhabits (fun _ : F => q931001_zeroV VE))
    (fun g : F -> E =>
      @q931001_is_local_inverse_at
        K E F KF VE VF f g point).

Theorem HasStrictFDerivAt_to_localInverse :
  forall
    (K E F : Type)
    (KF : q931001_nontrivially_normed_field K)
    (VE : @q931001_normed_space K E KF)
    (VF : @q931001_normed_space K F KF),
    q931001_complete VE ->
    forall
      (f : E -> F)
      (derivative :
        @q931001_continuous_linear_equiv K E F KF VE VF)
      (point : E),
      @q931001_has_strict_fderiv_at
        K E F KF VE VF f
        (q931001_cle_forward derivative) point ->
      @q931001_has_strict_fderiv_at
        K F E KF VF VE
        (@q931001_local_inverse K E F KF VE VF f point)
        (q931001_cle_inverse derivative) (f point).
Admitted.
