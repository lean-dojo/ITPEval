(*
  Statement-only formalization of Thousand Theorems corpus artifact Q848375
  (thousand-theorems__rocq__Q848375), "Implicit function theorem": two
  strictly Frechet-differentiable maps between complete normed spaces over an
  arbitrary nontrivially normed field, with surjective derivatives and
  complementary kernels, admit a local inverse whose curried form is the
  implicit function. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Definition q848375_set (A : Type) : Type := A -> Prop.

Record q848375_nontrivially_normed_field (K : Type) : Type := {
  q848375_zeroK : K;
  q848375_oneK : K;
  q848375_addK : K -> K -> K;
  q848375_mulK : K -> K -> K;
  q848375_negK : K -> K;
  q848375_invK : K -> K;
  q848375_normK : K -> R;
  q848375_zero_neq_oneK :
    q848375_zeroK <> q848375_oneK;
  q848375_addK_assoc :
    forall a b c : K,
      q848375_addK a (q848375_addK b c) =
      q848375_addK (q848375_addK a b) c;
  q848375_addK_comm :
    forall a b : K,
      q848375_addK a b = q848375_addK b a;
  q848375_addK_zero :
    forall a : K,
      q848375_addK a q848375_zeroK = a;
  q848375_addK_neg :
    forall a : K,
      q848375_addK a (q848375_negK a) = q848375_zeroK;
  q848375_mulK_assoc :
    forall a b c : K,
      q848375_mulK a (q848375_mulK b c) =
      q848375_mulK (q848375_mulK a b) c;
  q848375_mulK_comm :
    forall a b : K,
      q848375_mulK a b = q848375_mulK b a;
  q848375_mulK_one :
    forall a : K,
      q848375_mulK a q848375_oneK = a;
  q848375_mulK_add :
    forall a b c : K,
      q848375_mulK a (q848375_addK b c) =
      q848375_addK
        (q848375_mulK a b) (q848375_mulK a c);
  q848375_invK_zero :
    q848375_invK q848375_zeroK = q848375_zeroK;
  q848375_mulK_inv :
    forall a : K,
      a <> q848375_zeroK ->
      q848375_mulK a (q848375_invK a) = q848375_oneK;
  q848375_normK_nonnegative :
    forall a : K,
      0 <= q848375_normK a;
  q848375_normK_eq_zero :
    forall a : K,
      q848375_normK a = 0 <-> a = q848375_zeroK;
  q848375_normK_neg :
    forall a : K,
      q848375_normK (q848375_negK a) = q848375_normK a;
  q848375_normK_add_le :
    forall a b : K,
      q848375_normK (q848375_addK a b) <=
      q848375_normK a + q848375_normK b;
  q848375_normK_mul :
    forall a b : K,
      q848375_normK (q848375_mulK a b) =
      q848375_normK a * q848375_normK b;
  q848375_normK_nontrivial :
    exists a : K, 1 < q848375_normK a
}.

Arguments q848375_zeroK {K} _.
Arguments q848375_oneK {K} _.
Arguments q848375_addK {K} _ _ _.
Arguments q848375_mulK {K} _ _ _.
Arguments q848375_negK {K} _ _.
Arguments q848375_invK {K} _ _.
Arguments q848375_normK {K} _ _.

Record q848375_normed_space
    (K E : Type)
    (KF : q848375_nontrivially_normed_field K) : Type := {
  q848375_zeroV : E;
  q848375_addV : E -> E -> E;
  q848375_negV : E -> E;
  q848375_smulV : K -> E -> E;
  q848375_normV : E -> R;
  q848375_addV_assoc :
    forall x y z : E,
      q848375_addV x (q848375_addV y z) =
      q848375_addV (q848375_addV x y) z;
  q848375_addV_comm :
    forall x y : E,
      q848375_addV x y = q848375_addV y x;
  q848375_addV_zero :
    forall x : E,
      q848375_addV x q848375_zeroV = x;
  q848375_addV_neg :
    forall x : E,
      q848375_addV x (q848375_negV x) = q848375_zeroV;
  q848375_one_smul :
    forall x : E,
      q848375_smulV (q848375_oneK KF) x = x;
  q848375_mul_smul :
    forall (a b : K) (x : E),
      q848375_smulV (q848375_mulK KF a b) x =
      q848375_smulV a (q848375_smulV b x);
  q848375_add_smul :
    forall (a b : K) (x : E),
      q848375_smulV (q848375_addK KF a b) x =
      q848375_addV
        (q848375_smulV a x) (q848375_smulV b x);
  q848375_smul_add :
    forall (a : K) (x y : E),
      q848375_smulV a (q848375_addV x y) =
      q848375_addV
        (q848375_smulV a x) (q848375_smulV a y);
  q848375_zero_smul :
    forall x : E,
      q848375_smulV (q848375_zeroK KF) x = q848375_zeroV;
  q848375_smul_zero :
    forall a : K,
      q848375_smulV a q848375_zeroV = q848375_zeroV;
  q848375_normV_nonnegative :
    forall x : E,
      0 <= q848375_normV x;
  q848375_normV_eq_zero :
    forall x : E,
      q848375_normV x = 0 <-> x = q848375_zeroV;
  q848375_normV_neg :
    forall x : E,
      q848375_normV (q848375_negV x) = q848375_normV x;
  q848375_normV_add_le :
    forall x y : E,
      q848375_normV (q848375_addV x y) <=
      q848375_normV x + q848375_normV y;
  q848375_normV_smul :
    forall (a : K) (x : E),
      q848375_normV (q848375_smulV a x) =
      q848375_normK KF a * q848375_normV x
}.

Arguments q848375_zeroV {K E KF} _.
Arguments q848375_addV {K E KF} _ _ _.
Arguments q848375_negV {K E KF} _ _.
Arguments q848375_smulV {K E KF} _ _ _.
Arguments q848375_normV {K E KF} _ _.

Definition q848375_sub
    {K E : Type}
    {KF : q848375_nontrivially_normed_field K}
    (V : @q848375_normed_space K E KF)
    (x y : E) : E :=
  q848375_addV V x (q848375_negV V y).

Definition q848375_sequence_cauchy
    {K E : Type}
    {KF : q848375_nontrivially_normed_field K}
    (V : @q848375_normed_space K E KF)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q848375_normV V
          (q848375_sub V (u m) (u n)) < epsilon.

Definition q848375_sequence_converges
    {K E : Type}
    {KF : q848375_nontrivially_normed_field K}
    (V : @q848375_normed_space K E KF)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q848375_normV V
          (q848375_sub V (u n) limit) < epsilon.

Definition q848375_complete
    {K E : Type}
    {KF : q848375_nontrivially_normed_field K}
    (V : @q848375_normed_space K E KF) : Prop :=
  forall u : nat -> E,
    q848375_sequence_cauchy V u ->
    exists limit : E,
      q848375_sequence_converges V u limit.

Record q848375_continuous_linear_map
    (K E F : Type)
    (KF : q848375_nontrivially_normed_field K)
    (VE : @q848375_normed_space K E KF)
    (VF : @q848375_normed_space K F KF) : Type := {
  q848375_clm_fun : E -> F;
  q848375_clm_add :
    forall x y : E,
      q848375_clm_fun (q848375_addV VE x y) =
      q848375_addV VF
        (q848375_clm_fun x) (q848375_clm_fun y);
  q848375_clm_smul :
    forall (a : K) (x : E),
      q848375_clm_fun (q848375_smulV VE a x) =
      q848375_smulV VF a (q848375_clm_fun x);
  q848375_clm_bounded :
    exists bound : R,
      0 <= bound /\
      forall x : E,
        q848375_normV VF (q848375_clm_fun x) <=
        bound * q848375_normV VE x
}.

Arguments q848375_clm_fun {K E F KF VE VF} _ _.

Definition q848375_has_strict_fderiv_at
    {K E F : Type}
    {KF : q848375_nontrivially_normed_field K}
    (VE : @q848375_normed_space K E KF)
    (VF : @q848375_normed_space K F KF)
    (f : E -> F)
    (derivative :
      @q848375_continuous_linear_map K E F KF VE VF)
    (point : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall x y : E,
        q848375_normV VE (q848375_sub VE x point) < delta ->
        q848375_normV VE (q848375_sub VE y point) < delta ->
        q848375_normV VF
          (q848375_sub VF
            (q848375_sub VF (f x) (f y))
            (q848375_clm_fun derivative
              (q848375_sub VE x y))) <=
        epsilon * q848375_normV VE (q848375_sub VE x y).

Definition q848375_surjective
    {A B : Type} (f : A -> B) : Prop :=
  forall y : B, exists x : A, f x = y.

Definition q848375_complementary_kernels
    {K E F G : Type}
    {KF : q848375_nontrivially_normed_field K}
    (VE : @q848375_normed_space K E KF)
    (VF : @q848375_normed_space K F KF)
    (VG : @q848375_normed_space K G KF)
    (leftDeriv :
      @q848375_continuous_linear_map K E F KF VE VF)
    (rightDeriv :
      @q848375_continuous_linear_map K E G KF VE VG) : Prop :=
  (forall x : E,
    q848375_clm_fun leftDeriv x = q848375_zeroV VF ->
    q848375_clm_fun rightDeriv x = q848375_zeroV VG ->
    x = q848375_zeroV VE) /\
  forall x : E,
    exists u v : E,
      q848375_clm_fun leftDeriv u = q848375_zeroV VF /\
      q848375_clm_fun rightDeriv v = q848375_zeroV VG /\
      x = q848375_addV VE u v.

Definition q848375_open
    {K E : Type}
    {KF : q848375_nontrivially_normed_field K}
    (V : @q848375_normed_space K E KF)
    (U : q848375_set E) : Prop :=
  forall x : E,
    U x ->
    exists radius : R,
      0 < radius /\
      forall y : E,
        q848375_normV V (q848375_sub V y x) < radius ->
        U y.

Definition q848375_open_product
    {K F G : Type}
    {KF : q848375_nontrivially_normed_field K}
    (VF : @q848375_normed_space K F KF)
    (VG : @q848375_normed_space K G KF)
    (U : q848375_set (F * G)) : Prop :=
  forall p : F * G,
    U p ->
    exists radius : R,
      0 < radius /\
      forall q : F * G,
        q848375_normV VF
          (q848375_sub VF (fst q) (fst p)) < radius ->
        q848375_normV VG
          (q848375_sub VG (snd q) (snd p)) < radius ->
        U q.

Definition q848375_forward_continuous_on
    {K E F G : Type}
    {KF : q848375_nontrivially_normed_field K}
    (VE : @q848375_normed_space K E KF)
    (VF : @q848375_normed_space K F KF)
    (VG : @q848375_normed_space K G KF)
    (leftFun : E -> F)
    (rightFun : E -> G)
    (source : q848375_set E) : Prop :=
  forall x : E,
    source x ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall y : E,
          source y ->
          q848375_normV VE
            (q848375_sub VE y x) < delta ->
          q848375_normV VF
            (q848375_sub VF (leftFun y) (leftFun x)) < epsilon /\
          q848375_normV VG
            (q848375_sub VG (rightFun y) (rightFun x)) < epsilon.

Definition q848375_inverse_continuous_on
    {K E F G : Type}
    {KF : q848375_nontrivially_normed_field K}
    (VE : @q848375_normed_space K E KF)
    (VF : @q848375_normed_space K F KF)
    (VG : @q848375_normed_space K G KF)
    (implicitFunction : F -> G -> E)
    (target : q848375_set (F * G)) : Prop :=
  forall p : F * G,
    target p ->
    forall epsilon : R,
      0 < epsilon ->
      exists delta : R,
        0 < delta /\
        forall q : F * G,
          target q ->
          q848375_normV VF
            (q848375_sub VF (fst q) (fst p)) < delta ->
          q848375_normV VG
            (q848375_sub VG (snd q) (snd p)) < delta ->
          q848375_normV VE
            (q848375_sub VE
              (implicitFunction (fst q) (snd q))
              (implicitFunction (fst p) (snd p))) < epsilon.

Theorem q848375_implicit_function_theorem :
  forall
    (K E F G : Type)
    (KF : q848375_nontrivially_normed_field K)
    (VE : @q848375_normed_space K E KF)
    (VF : @q848375_normed_space K F KF)
    (VG : @q848375_normed_space K G KF),
    q848375_complete VE ->
    q848375_complete VF ->
    q848375_complete VG ->
    forall
      (leftFun : E -> F)
      (leftDeriv :
        @q848375_continuous_linear_map K E F KF VE VF)
      (rightFun : E -> G)
      (rightDeriv :
        @q848375_continuous_linear_map K E G KF VE VG)
      (point : E),
      @q848375_has_strict_fderiv_at
        K E F KF VE VF leftFun leftDeriv point ->
      @q848375_has_strict_fderiv_at
        K E G KF VE VG rightFun rightDeriv point ->
      q848375_surjective (q848375_clm_fun leftDeriv) ->
      q848375_surjective (q848375_clm_fun rightDeriv) ->
      @q848375_complementary_kernels
        K E F G KF VE VF VG leftDeriv rightDeriv ->
      exists
        (implicitFunction : F -> G -> E)
        (source : q848375_set E)
        (target : q848375_set (F * G)),
        @q848375_open K E KF VE source /\
        @q848375_open_product K F G KF VF VG target /\
        source point /\
        target (leftFun point, rightFun point) /\
        @q848375_forward_continuous_on
          K E F G KF VE VF VG leftFun rightFun source /\
        @q848375_inverse_continuous_on
          K E F G KF VE VF VG implicitFunction target /\
        (forall x : E,
          source x ->
          target (leftFun x, rightFun x) /\
          implicitFunction (leftFun x) (rightFun x) = x) /\
        forall p : F * G,
          target p ->
          source (implicitFunction (fst p) (snd p)) /\
          leftFun (implicitFunction (fst p) (snd p)) = fst p /\
          rightFun (implicitFunction (fst p) (snd p)) = snd p.
Admitted.
