(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1472120
  (thousand-theorems__rocq__Q1472120), "Hellinger&ndash;Toeplitz theorem":
  every everywhere-defined symmetric linear operator on a complete real-or-
  complex inner-product space is continuous. This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1472120_rclike (K : Type) : Type := {
  q1472120_k_zero : K;
  q1472120_k_one : K;
  q1472120_k_add : K -> K -> K;
  q1472120_k_mul : K -> K -> K;
  q1472120_k_neg : K -> K;
  q1472120_k_inv : K -> K;
  q1472120_k_conj : K -> K;
  q1472120_k_norm : K -> R;
  q1472120_k_of_real : R -> K;
  q1472120_k_re : K -> R;
  q1472120_k_im : K -> R;
  q1472120_k_I : K;

  q1472120_k_add_assoc :
    forall x y z : K,
      q1472120_k_add x (q1472120_k_add y z) =
      q1472120_k_add (q1472120_k_add x y) z;
  q1472120_k_add_comm :
    forall x y : K, q1472120_k_add x y = q1472120_k_add y x;
  q1472120_k_add_zero :
    forall x : K, q1472120_k_add x q1472120_k_zero = x;
  q1472120_k_add_neg :
    forall x : K,
      q1472120_k_add x (q1472120_k_neg x) = q1472120_k_zero;
  q1472120_k_mul_assoc :
    forall x y z : K,
      q1472120_k_mul x (q1472120_k_mul y z) =
      q1472120_k_mul (q1472120_k_mul x y) z;
  q1472120_k_mul_comm :
    forall x y : K, q1472120_k_mul x y = q1472120_k_mul y x;
  q1472120_k_mul_one :
    forall x : K, q1472120_k_mul x q1472120_k_one = x;
  q1472120_k_left_distrib :
    forall x y z : K,
      q1472120_k_mul x (q1472120_k_add y z) =
      q1472120_k_add
        (q1472120_k_mul x y) (q1472120_k_mul x z);
  q1472120_k_mul_inv :
    forall x : K, x <> q1472120_k_zero ->
      q1472120_k_mul x (q1472120_k_inv x) = q1472120_k_one;
  q1472120_k_nontrivial :
    q1472120_k_zero <> q1472120_k_one;

  q1472120_k_conj_add :
    forall x y : K,
      q1472120_k_conj (q1472120_k_add x y) =
      q1472120_k_add (q1472120_k_conj x) (q1472120_k_conj y);
  q1472120_k_conj_mul :
    forall x y : K,
      q1472120_k_conj (q1472120_k_mul x y) =
      q1472120_k_mul (q1472120_k_conj x) (q1472120_k_conj y);
  q1472120_k_conj_involutive :
    forall x : K, q1472120_k_conj (q1472120_k_conj x) = x;

  q1472120_k_norm_nonnegative :
    forall x : K, 0 <= q1472120_k_norm x;
  q1472120_k_norm_eq_zero :
    forall x : K,
      q1472120_k_norm x = 0 <-> x = q1472120_k_zero;
  q1472120_k_norm_add_le :
    forall x y : K,
      q1472120_k_norm (q1472120_k_add x y) <=
      q1472120_k_norm x + q1472120_k_norm y;
  q1472120_k_norm_mul :
    forall x y : K,
      q1472120_k_norm (q1472120_k_mul x y) =
      q1472120_k_norm x * q1472120_k_norm y;
  q1472120_k_norm_conj :
    forall x : K,
      q1472120_k_norm (q1472120_k_conj x) = q1472120_k_norm x;

  q1472120_k_of_real_zero :
    q1472120_k_of_real 0 = q1472120_k_zero;
  q1472120_k_of_real_one :
    q1472120_k_of_real 1 = q1472120_k_one;
  q1472120_k_of_real_add :
    forall a b : R,
      q1472120_k_of_real (a + b) =
      q1472120_k_add (q1472120_k_of_real a) (q1472120_k_of_real b);
  q1472120_k_of_real_mul :
    forall a b : R,
      q1472120_k_of_real (a * b) =
      q1472120_k_mul (q1472120_k_of_real a) (q1472120_k_of_real b);
  q1472120_k_of_real_neg :
    forall a : R,
      q1472120_k_of_real (- a) =
      q1472120_k_neg (q1472120_k_of_real a);
  q1472120_k_of_real_injective :
    forall a b : R,
      q1472120_k_of_real a = q1472120_k_of_real b -> a = b;
  q1472120_k_norm_of_real :
    forall a : R, q1472120_k_norm (q1472120_k_of_real a) = Rabs a;

  q1472120_k_re_of_real :
    forall a : R, q1472120_k_re (q1472120_k_of_real a) = a;
  q1472120_k_im_of_real :
    forall a : R, q1472120_k_im (q1472120_k_of_real a) = 0;
  q1472120_k_re_add :
    forall x y : K,
      q1472120_k_re (q1472120_k_add x y) =
      q1472120_k_re x + q1472120_k_re y;
  q1472120_k_im_add :
    forall x y : K,
      q1472120_k_im (q1472120_k_add x y) =
      q1472120_k_im x + q1472120_k_im y;
  q1472120_k_re_mul :
    forall x y : K,
      q1472120_k_re (q1472120_k_mul x y) =
      q1472120_k_re x * q1472120_k_re y -
      q1472120_k_im x * q1472120_k_im y;
  q1472120_k_im_mul :
    forall x y : K,
      q1472120_k_im (q1472120_k_mul x y) =
      q1472120_k_re x * q1472120_k_im y +
      q1472120_k_im x * q1472120_k_re y;
  q1472120_k_re_conj :
    forall x : K, q1472120_k_re (q1472120_k_conj x) = q1472120_k_re x;
  q1472120_k_im_conj :
    forall x : K, q1472120_k_im (q1472120_k_conj x) = - q1472120_k_im x;
  q1472120_k_re_I :
    q1472120_k_re q1472120_k_I = 0;
  q1472120_k_im_I_real :
    q1472120_k_I = q1472120_k_zero -> q1472120_k_im q1472120_k_I = 0;
  q1472120_k_im_I_complex :
    q1472120_k_I <> q1472120_k_zero -> q1472120_k_im q1472120_k_I = 1;
  q1472120_k_I_cases :
    q1472120_k_I = q1472120_k_zero \/
    (q1472120_k_I <> q1472120_k_zero /\
     q1472120_k_mul q1472120_k_I q1472120_k_I =
       q1472120_k_neg q1472120_k_one);
  q1472120_k_coordinate_decomposition :
    forall x : K,
      x =
      q1472120_k_add
        (q1472120_k_of_real (q1472120_k_re x))
        (q1472120_k_mul
          (q1472120_k_of_real (q1472120_k_im x))
          q1472120_k_I);
  q1472120_k_norm_coordinates :
    forall x : K,
      q1472120_k_norm x =
      sqrt (q1472120_k_re x * q1472120_k_re x +
            q1472120_k_im x * q1472120_k_im x)
}.

Arguments q1472120_k_zero {K} _.
Arguments q1472120_k_one {K} _.
Arguments q1472120_k_add {K} _ _ _.
Arguments q1472120_k_mul {K} _ _ _.
Arguments q1472120_k_neg {K} _ _.
Arguments q1472120_k_conj {K} _ _.
Arguments q1472120_k_norm {K} _ _.
Arguments q1472120_k_of_real {K} _ _.
Arguments q1472120_k_re {K} _ _.

Record q1472120_inner_product_space
    (K : Type) (F : q1472120_rclike K) (E : Type) : Type := {
  q1472120_e_zero : E;
  q1472120_e_add : E -> E -> E;
  q1472120_e_neg : E -> E;
  q1472120_e_smul : K -> E -> E;
  q1472120_e_norm : E -> R;
  q1472120_e_inner : E -> E -> K;

  q1472120_e_add_assoc :
    forall x y z : E,
      q1472120_e_add x (q1472120_e_add y z) =
      q1472120_e_add (q1472120_e_add x y) z;
  q1472120_e_add_comm :
    forall x y : E, q1472120_e_add x y = q1472120_e_add y x;
  q1472120_e_add_zero :
    forall x : E, q1472120_e_add x q1472120_e_zero = x;
  q1472120_e_add_neg :
    forall x : E,
      q1472120_e_add x (q1472120_e_neg x) = q1472120_e_zero;

  q1472120_e_one_smul :
    forall x : E, q1472120_e_smul (q1472120_k_one F) x = x;
  q1472120_e_mul_smul :
    forall (a b : K) (x : E),
      q1472120_e_smul (q1472120_k_mul F a b) x =
      q1472120_e_smul a (q1472120_e_smul b x);
  q1472120_e_add_smul :
    forall (a b : K) (x : E),
      q1472120_e_smul (q1472120_k_add F a b) x =
      q1472120_e_add
        (q1472120_e_smul a x) (q1472120_e_smul b x);
  q1472120_e_smul_add :
    forall (a : K) (x y : E),
      q1472120_e_smul a (q1472120_e_add x y) =
      q1472120_e_add
        (q1472120_e_smul a x) (q1472120_e_smul a y);

  q1472120_e_norm_nonnegative :
    forall x : E, 0 <= q1472120_e_norm x;
  q1472120_e_norm_eq_zero :
    forall x : E, q1472120_e_norm x = 0 <-> x = q1472120_e_zero;
  q1472120_e_norm_neg :
    forall x : E, q1472120_e_norm (q1472120_e_neg x) = q1472120_e_norm x;
  q1472120_e_norm_add_le :
    forall x y : E,
      q1472120_e_norm (q1472120_e_add x y) <=
      q1472120_e_norm x + q1472120_e_norm y;
  q1472120_e_norm_smul :
    forall (a : K) (x : E),
      q1472120_e_norm (q1472120_e_smul a x) =
      q1472120_k_norm F a * q1472120_e_norm x;

  q1472120_e_inner_add_left :
    forall x y z : E,
      q1472120_e_inner (q1472120_e_add x y) z =
      q1472120_k_add F
        (q1472120_e_inner x z) (q1472120_e_inner y z);
  q1472120_e_inner_add_right :
    forall x y z : E,
      q1472120_e_inner x (q1472120_e_add y z) =
      q1472120_k_add F
        (q1472120_e_inner x y) (q1472120_e_inner x z);
  q1472120_e_inner_smul_left :
    forall (a : K) (x y : E),
      q1472120_e_inner (q1472120_e_smul a x) y =
      q1472120_k_mul F
        (q1472120_k_conj F a) (q1472120_e_inner x y);
  q1472120_e_inner_smul_right :
    forall (a : K) (x y : E),
      q1472120_e_inner x (q1472120_e_smul a y) =
      q1472120_k_mul F a (q1472120_e_inner x y);
  q1472120_e_inner_conj_symm :
    forall x y : E,
      q1472120_e_inner y x =
      q1472120_k_conj F (q1472120_e_inner x y);
  q1472120_e_inner_nonnegative :
    forall x : E,
      exists r : R,
        0 <= r /\
        q1472120_e_inner x x = q1472120_k_of_real F r;
  q1472120_e_inner_eq_zero :
    forall x : E,
      q1472120_e_inner x x = q1472120_k_zero F <->
      x = q1472120_e_zero;
  q1472120_e_norm_sq :
    forall x : E,
      q1472120_e_norm x * q1472120_e_norm x =
      q1472120_k_re F (q1472120_e_inner x x)
}.

Arguments q1472120_e_zero {K F E} _.
Arguments q1472120_e_add {K F E} _ _ _.
Arguments q1472120_e_neg {K F E} _ _.
Arguments q1472120_e_smul {K F E} _ _ _.
Arguments q1472120_e_norm {K F E} _ _.
Arguments q1472120_e_inner {K F E} _ _ _.

Definition q1472120_e_sub
    {K E : Type}
    {F : q1472120_rclike K}
    (H : q1472120_inner_product_space F E)
    (x y : E) : E :=
  q1472120_e_add H x (q1472120_e_neg H y).

Definition q1472120_sequence_converges
    {K E : Type}
    {F : q1472120_rclike K}
    (H : q1472120_inner_product_space F E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1472120_e_norm H
          (q1472120_e_sub H (u n) limit) < epsilon.

Definition q1472120_sequence_cauchy
    {K E : Type}
    {F : q1472120_rclike K}
    (H : q1472120_inner_product_space F E)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q1472120_e_norm H
          (q1472120_e_sub H (u m) (u n)) < epsilon.

Definition q1472120_complete
    {K E : Type}
    {F : q1472120_rclike K}
    (H : q1472120_inner_product_space F E) : Prop :=
  forall u : nat -> E,
    q1472120_sequence_cauchy H u ->
    exists limit : E, q1472120_sequence_converges H u limit.

Record q1472120_linear_endomorphism
    {K E : Type}
    {F : q1472120_rclike K}
    (H : q1472120_inner_product_space F E) : Type := {
  q1472120_map_fun : E -> E;
  q1472120_map_add :
    forall x y : E,
      q1472120_map_fun (q1472120_e_add H x y) =
      q1472120_e_add H (q1472120_map_fun x) (q1472120_map_fun y);
  q1472120_map_smul :
    forall (a : K) (x : E),
      q1472120_map_fun (q1472120_e_smul H a x) =
      q1472120_e_smul H a (q1472120_map_fun x)
}.

Arguments q1472120_map_fun {K E F H} _ _.

Definition q1472120_is_symmetric
    {K E : Type}
    {F : q1472120_rclike K}
    {H : q1472120_inner_product_space F E}
    (T : q1472120_linear_endomorphism H) : Prop :=
  forall x y : E,
    q1472120_e_inner H (q1472120_map_fun T x) y =
    q1472120_e_inner H x (q1472120_map_fun T y).

Definition q1472120_is_continuous
    {K E : Type}
    {F : q1472120_rclike K}
    (H : q1472120_inner_product_space F E)
    (T : q1472120_linear_endomorphism H) : Prop :=
  forall (x : E) (epsilon : R),
    0 < epsilon ->
    exists delta : R,
      0 < delta /\
      forall y : E,
        q1472120_e_norm H (q1472120_e_sub H y x) < delta ->
        q1472120_e_norm H
          (q1472120_e_sub H
            (q1472120_map_fun T y) (q1472120_map_fun T x)) < epsilon.

Theorem LinearMap_IsSymmetric_continuous :
  forall (K E : Type)
         (F : q1472120_rclike K)
         (H : q1472120_inner_product_space F E)
         (T : q1472120_linear_endomorphism H),
    q1472120_complete H ->
    q1472120_is_symmetric T ->
    @q1472120_is_continuous K E F H T.
Admitted.
