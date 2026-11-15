(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1357684
  (thousand-theorems__rocq__Q1357684), "Riesz representation theorem": the
  canonical inner-product map from a complete real-or-complex inner-product
  space to its continuous dual is a conjugate-linear isometric equivalence.
  This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1357684_rclike (K : Type) : Type := {
  q1357684_k_zero : K;
  q1357684_k_one : K;
  q1357684_k_add : K -> K -> K;
  q1357684_k_mul : K -> K -> K;
  q1357684_k_neg : K -> K;
  q1357684_k_inv : K -> K;
  q1357684_k_conj : K -> K;
  q1357684_k_norm : K -> R;
  q1357684_k_of_real : R -> K;
  q1357684_k_re : K -> R;
  q1357684_k_im : K -> R;
  q1357684_k_I : K;

  q1357684_k_add_assoc :
    forall x y z : K,
      q1357684_k_add x (q1357684_k_add y z) =
      q1357684_k_add (q1357684_k_add x y) z;
  q1357684_k_add_comm :
    forall x y : K, q1357684_k_add x y = q1357684_k_add y x;
  q1357684_k_add_zero :
    forall x : K, q1357684_k_add x q1357684_k_zero = x;
  q1357684_k_add_neg :
    forall x : K,
      q1357684_k_add x (q1357684_k_neg x) = q1357684_k_zero;
  q1357684_k_mul_assoc :
    forall x y z : K,
      q1357684_k_mul x (q1357684_k_mul y z) =
      q1357684_k_mul (q1357684_k_mul x y) z;
  q1357684_k_mul_comm :
    forall x y : K, q1357684_k_mul x y = q1357684_k_mul y x;
  q1357684_k_mul_one :
    forall x : K, q1357684_k_mul x q1357684_k_one = x;
  q1357684_k_left_distrib :
    forall x y z : K,
      q1357684_k_mul x (q1357684_k_add y z) =
      q1357684_k_add
        (q1357684_k_mul x y) (q1357684_k_mul x z);
  q1357684_k_mul_inv :
    forall x : K, x <> q1357684_k_zero ->
      q1357684_k_mul x (q1357684_k_inv x) = q1357684_k_one;
  q1357684_k_nontrivial :
    q1357684_k_zero <> q1357684_k_one;

  q1357684_k_conj_add :
    forall x y : K,
      q1357684_k_conj (q1357684_k_add x y) =
      q1357684_k_add (q1357684_k_conj x) (q1357684_k_conj y);
  q1357684_k_conj_mul :
    forall x y : K,
      q1357684_k_conj (q1357684_k_mul x y) =
      q1357684_k_mul (q1357684_k_conj x) (q1357684_k_conj y);
  q1357684_k_conj_involutive :
    forall x : K, q1357684_k_conj (q1357684_k_conj x) = x;

  q1357684_k_norm_nonnegative :
    forall x : K, 0 <= q1357684_k_norm x;
  q1357684_k_norm_eq_zero :
    forall x : K,
      q1357684_k_norm x = 0 <-> x = q1357684_k_zero;
  q1357684_k_norm_add_le :
    forall x y : K,
      q1357684_k_norm (q1357684_k_add x y) <=
      q1357684_k_norm x + q1357684_k_norm y;
  q1357684_k_norm_mul :
    forall x y : K,
      q1357684_k_norm (q1357684_k_mul x y) =
      q1357684_k_norm x * q1357684_k_norm y;
  q1357684_k_norm_conj :
    forall x : K,
      q1357684_k_norm (q1357684_k_conj x) = q1357684_k_norm x;

  q1357684_k_of_real_zero :
    q1357684_k_of_real 0 = q1357684_k_zero;
  q1357684_k_of_real_one :
    q1357684_k_of_real 1 = q1357684_k_one;
  q1357684_k_of_real_add :
    forall a b : R,
      q1357684_k_of_real (a + b) =
      q1357684_k_add (q1357684_k_of_real a) (q1357684_k_of_real b);
  q1357684_k_of_real_mul :
    forall a b : R,
      q1357684_k_of_real (a * b) =
      q1357684_k_mul (q1357684_k_of_real a) (q1357684_k_of_real b);
  q1357684_k_of_real_neg :
    forall a : R,
      q1357684_k_of_real (- a) =
      q1357684_k_neg (q1357684_k_of_real a);
  q1357684_k_of_real_injective :
    forall a b : R,
      q1357684_k_of_real a = q1357684_k_of_real b -> a = b;
  q1357684_k_norm_of_real :
    forall a : R, q1357684_k_norm (q1357684_k_of_real a) = Rabs a;

  q1357684_k_re_of_real :
    forall a : R, q1357684_k_re (q1357684_k_of_real a) = a;
  q1357684_k_im_of_real :
    forall a : R, q1357684_k_im (q1357684_k_of_real a) = 0;
  q1357684_k_re_add :
    forall x y : K,
      q1357684_k_re (q1357684_k_add x y) =
      q1357684_k_re x + q1357684_k_re y;
  q1357684_k_im_add :
    forall x y : K,
      q1357684_k_im (q1357684_k_add x y) =
      q1357684_k_im x + q1357684_k_im y;
  q1357684_k_re_mul :
    forall x y : K,
      q1357684_k_re (q1357684_k_mul x y) =
      q1357684_k_re x * q1357684_k_re y -
      q1357684_k_im x * q1357684_k_im y;
  q1357684_k_im_mul :
    forall x y : K,
      q1357684_k_im (q1357684_k_mul x y) =
      q1357684_k_re x * q1357684_k_im y +
      q1357684_k_im x * q1357684_k_re y;
  q1357684_k_re_conj :
    forall x : K, q1357684_k_re (q1357684_k_conj x) = q1357684_k_re x;
  q1357684_k_im_conj :
    forall x : K, q1357684_k_im (q1357684_k_conj x) = - q1357684_k_im x;
  q1357684_k_re_I :
    q1357684_k_re q1357684_k_I = 0;
  q1357684_k_im_I_real :
    q1357684_k_I = q1357684_k_zero -> q1357684_k_im q1357684_k_I = 0;
  q1357684_k_im_I_complex :
    q1357684_k_I <> q1357684_k_zero -> q1357684_k_im q1357684_k_I = 1;
  q1357684_k_I_cases :
    q1357684_k_I = q1357684_k_zero \/
    (q1357684_k_I <> q1357684_k_zero /\
     q1357684_k_mul q1357684_k_I q1357684_k_I =
       q1357684_k_neg q1357684_k_one);
  q1357684_k_coordinate_decomposition :
    forall x : K,
      x =
      q1357684_k_add
        (q1357684_k_of_real (q1357684_k_re x))
        (q1357684_k_mul
          (q1357684_k_of_real (q1357684_k_im x))
          q1357684_k_I);
  q1357684_k_norm_coordinates :
    forall x : K,
      q1357684_k_norm x =
      sqrt (q1357684_k_re x * q1357684_k_re x +
            q1357684_k_im x * q1357684_k_im x)
}.

Arguments q1357684_k_zero {K} _.
Arguments q1357684_k_one {K} _.
Arguments q1357684_k_add {K} _ _ _.
Arguments q1357684_k_mul {K} _ _ _.
Arguments q1357684_k_neg {K} _ _.
Arguments q1357684_k_inv {K} _ _.
Arguments q1357684_k_conj {K} _ _.
Arguments q1357684_k_norm {K} _ _.
Arguments q1357684_k_of_real {K} _ _.
Arguments q1357684_k_re {K} _ _.
Arguments q1357684_k_im {K} _ _.
Arguments q1357684_k_I {K} _.

Record q1357684_inner_product_space
    (K : Type) (F : q1357684_rclike K) (E : Type) : Type := {
  q1357684_e_zero : E;
  q1357684_e_add : E -> E -> E;
  q1357684_e_neg : E -> E;
  q1357684_e_smul : K -> E -> E;
  q1357684_e_norm : E -> R;
  q1357684_e_inner : E -> E -> K;

  q1357684_e_add_assoc :
    forall x y z : E,
      q1357684_e_add x (q1357684_e_add y z) =
      q1357684_e_add (q1357684_e_add x y) z;
  q1357684_e_add_comm :
    forall x y : E, q1357684_e_add x y = q1357684_e_add y x;
  q1357684_e_add_zero :
    forall x : E, q1357684_e_add x q1357684_e_zero = x;
  q1357684_e_add_neg :
    forall x : E,
      q1357684_e_add x (q1357684_e_neg x) = q1357684_e_zero;

  q1357684_e_one_smul :
    forall x : E, q1357684_e_smul (q1357684_k_one F) x = x;
  q1357684_e_mul_smul :
    forall (a b : K) (x : E),
      q1357684_e_smul (q1357684_k_mul F a b) x =
      q1357684_e_smul a (q1357684_e_smul b x);
  q1357684_e_add_smul :
    forall (a b : K) (x : E),
      q1357684_e_smul (q1357684_k_add F a b) x =
      q1357684_e_add
        (q1357684_e_smul a x) (q1357684_e_smul b x);
  q1357684_e_smul_add :
    forall (a : K) (x y : E),
      q1357684_e_smul a (q1357684_e_add x y) =
      q1357684_e_add
        (q1357684_e_smul a x) (q1357684_e_smul a y);
  q1357684_e_zero_smul :
    forall x : E,
      q1357684_e_smul (q1357684_k_zero F) x = q1357684_e_zero;
  q1357684_e_smul_zero :
    forall a : K, q1357684_e_smul a q1357684_e_zero = q1357684_e_zero;

  q1357684_e_norm_nonnegative :
    forall x : E, 0 <= q1357684_e_norm x;
  q1357684_e_norm_eq_zero :
    forall x : E, q1357684_e_norm x = 0 <-> x = q1357684_e_zero;
  q1357684_e_norm_add_le :
    forall x y : E,
      q1357684_e_norm (q1357684_e_add x y) <=
      q1357684_e_norm x + q1357684_e_norm y;
  q1357684_e_norm_smul :
    forall (a : K) (x : E),
      q1357684_e_norm (q1357684_e_smul a x) =
      q1357684_k_norm F a * q1357684_e_norm x;

  q1357684_e_inner_add_left :
    forall x y z : E,
      q1357684_e_inner (q1357684_e_add x y) z =
      q1357684_k_add F
        (q1357684_e_inner x z) (q1357684_e_inner y z);
  q1357684_e_inner_add_right :
    forall x y z : E,
      q1357684_e_inner x (q1357684_e_add y z) =
      q1357684_k_add F
        (q1357684_e_inner x y) (q1357684_e_inner x z);
  q1357684_e_inner_smul_left :
    forall (a : K) (x y : E),
      q1357684_e_inner (q1357684_e_smul a x) y =
      q1357684_k_mul F
        (q1357684_k_conj F a) (q1357684_e_inner x y);
  q1357684_e_inner_smul_right :
    forall (a : K) (x y : E),
      q1357684_e_inner x (q1357684_e_smul a y) =
      q1357684_k_mul F a (q1357684_e_inner x y);
  q1357684_e_inner_conj_symm :
    forall x y : E,
      q1357684_e_inner y x =
      q1357684_k_conj F (q1357684_e_inner x y);
  q1357684_e_inner_nonnegative :
    forall x : E,
      exists r : R,
        0 <= r /\
        q1357684_e_inner x x = q1357684_k_of_real F r;
  q1357684_e_inner_eq_zero :
    forall x : E,
      q1357684_e_inner x x = q1357684_k_zero F <->
      x = q1357684_e_zero;
  q1357684_e_norm_sq :
    forall x : E,
      q1357684_e_norm x * q1357684_e_norm x =
      q1357684_k_re F (q1357684_e_inner x x)
}.

Arguments q1357684_e_zero {K F E} _.
Arguments q1357684_e_add {K F E} _ _ _.
Arguments q1357684_e_neg {K F E} _ _.
Arguments q1357684_e_smul {K F E} _ _ _.
Arguments q1357684_e_norm {K F E} _ _.
Arguments q1357684_e_inner {K F E} _ _ _.

Definition q1357684_e_sub
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E)
    (x y : E) : E :=
  q1357684_e_add H x (q1357684_e_neg H y).

Definition q1357684_sequence_converges
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      q1357684_e_norm H (q1357684_e_sub H (u n) limit) < epsilon.

Definition q1357684_sequence_cauchy
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E)
    (u : nat -> E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat ->
      (N <= n)%nat ->
      q1357684_e_norm H (q1357684_e_sub H (u m) (u n)) < epsilon.

Definition q1357684_complete
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E) : Prop :=
  forall u : nat -> E,
    q1357684_sequence_cauchy H u ->
    exists limit : E, q1357684_sequence_converges H u limit.

Definition q1357684_continuous_linear_functional
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E)
    (ell : E -> K) : Prop :=
  (forall x y : E,
    ell (q1357684_e_add H x y) =
    q1357684_k_add F (ell x) (ell y)) /\
  (forall (a : K) (x : E),
    ell (q1357684_e_smul H a x) =
    q1357684_k_mul F a (ell x)) /\
  exists bound : R,
    0 <= bound /\
    forall x : E,
      q1357684_k_norm F (ell x) <= bound * q1357684_e_norm H x.

Definition q1357684_dual_norm_has_value
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E)
    (ell : E -> K) (value : R) : Prop :=
  0 <= value /\
  (forall x : E,
    q1357684_k_norm F (ell x) <= value * q1357684_e_norm H x) /\
  forall bound : R,
    0 <= bound ->
    (forall x : E,
      q1357684_k_norm F (ell x) <= bound * q1357684_e_norm H x) ->
    value <= bound.

Definition q1357684_to_dual_map
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E)
    (x y : E) : K :=
  q1357684_e_inner H x y.

Definition q1357684_is_conjugate_linear_isometric_equivalence
    {K E : Type}
    {F : q1357684_rclike K}
    (H : q1357684_inner_product_space F E) : Prop :=
  (forall x : E,
    q1357684_continuous_linear_functional H
      (q1357684_to_dual_map H x)) /\
  (forall x y z : E,
    q1357684_to_dual_map H (q1357684_e_add H x y) z =
    q1357684_k_add F
      (q1357684_to_dual_map H x z)
      (q1357684_to_dual_map H y z)) /\
  (forall (a : K) (x z : E),
    q1357684_to_dual_map H (q1357684_e_smul H a x) z =
    q1357684_k_mul F
      (q1357684_k_conj F a)
      (q1357684_to_dual_map H x z)) /\
  (forall x : E,
    q1357684_dual_norm_has_value H
      (q1357684_to_dual_map H x) (q1357684_e_norm H x)) /\
  (forall x y : E,
    (forall z : E,
      q1357684_to_dual_map H x z =
      q1357684_to_dual_map H y z) ->
    x = y) /\
  forall ell : E -> K,
    q1357684_continuous_linear_functional H ell ->
    exists x : E,
      forall y : E, q1357684_to_dual_map H x y = ell y.

Theorem InnerProductSpace_toDual :
  forall (K E : Type)
         (F : q1357684_rclike K)
         (H : q1357684_inner_product_space F E),
    q1357684_complete H ->
    q1357684_is_conjugate_linear_isometric_equivalence H.
Admitted.
