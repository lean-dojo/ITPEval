(*
  Statement-only formalization of Thousand Theorems corpus artifact Q866116
  (thousand-theorems__rocq__Q866116), "Hahn-Banach theorem": every continuous
  linear functional on a subspace of a real-or-complex seminormed vector space
  extends to the whole space without changing its operator norm.
  This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q866116_rclike (K : Type) : Type := {
  q866116_k_zero : K;
  q866116_k_one : K;
  q866116_k_add : K -> K -> K;
  q866116_k_mul : K -> K -> K;
  q866116_k_neg : K -> K;
  q866116_k_inv : K -> K;
  q866116_k_conj : K -> K;
  q866116_k_norm : K -> R;
  q866116_k_of_real : R -> K;
  q866116_k_re : K -> R;
  q866116_k_im : K -> R;
  q866116_k_I : K;

  q866116_k_add_assoc :
    forall x y z : K,
      q866116_k_add x (q866116_k_add y z) =
      q866116_k_add (q866116_k_add x y) z;
  q866116_k_add_comm :
    forall x y : K,
      q866116_k_add x y = q866116_k_add y x;
  q866116_k_add_zero :
    forall x : K,
      q866116_k_add x q866116_k_zero = x;
  q866116_k_add_neg :
    forall x : K,
      q866116_k_add x (q866116_k_neg x) = q866116_k_zero;
  q866116_k_mul_assoc :
    forall x y z : K,
      q866116_k_mul x (q866116_k_mul y z) =
      q866116_k_mul (q866116_k_mul x y) z;
  q866116_k_mul_comm :
    forall x y : K,
      q866116_k_mul x y = q866116_k_mul y x;
  q866116_k_mul_one :
    forall x : K,
      q866116_k_mul x q866116_k_one = x;
  q866116_k_left_distrib :
    forall x y z : K,
      q866116_k_mul x (q866116_k_add y z) =
      q866116_k_add
        (q866116_k_mul x y) (q866116_k_mul x z);
  q866116_k_inv_zero :
    q866116_k_inv q866116_k_zero = q866116_k_zero;
  q866116_k_mul_inv :
    forall x : K,
      x <> q866116_k_zero ->
      q866116_k_mul x (q866116_k_inv x) = q866116_k_one;
  q866116_k_nontrivial :
    q866116_k_zero <> q866116_k_one;

  q866116_k_conj_add :
    forall x y : K,
      q866116_k_conj (q866116_k_add x y) =
      q866116_k_add (q866116_k_conj x) (q866116_k_conj y);
  q866116_k_conj_mul :
    forall x y : K,
      q866116_k_conj (q866116_k_mul x y) =
      q866116_k_mul (q866116_k_conj x) (q866116_k_conj y);
  q866116_k_conj_involutive :
    forall x : K,
      q866116_k_conj (q866116_k_conj x) = x;

  q866116_k_norm_nonnegative :
    forall x : K,
      0 <= q866116_k_norm x;
  q866116_k_norm_eq_zero :
    forall x : K,
      q866116_k_norm x = 0 <-> x = q866116_k_zero;
  q866116_k_norm_add_le :
    forall x y : K,
      q866116_k_norm (q866116_k_add x y) <=
      q866116_k_norm x + q866116_k_norm y;
  q866116_k_norm_mul :
    forall x y : K,
      q866116_k_norm (q866116_k_mul x y) =
      q866116_k_norm x * q866116_k_norm y;
  q866116_k_norm_conj :
    forall x : K,
      q866116_k_norm (q866116_k_conj x) = q866116_k_norm x;

  q866116_k_of_real_zero :
    q866116_k_of_real 0 = q866116_k_zero;
  q866116_k_of_real_one :
    q866116_k_of_real 1 = q866116_k_one;
  q866116_k_of_real_add :
    forall a b : R,
      q866116_k_of_real (a + b) =
      q866116_k_add (q866116_k_of_real a) (q866116_k_of_real b);
  q866116_k_of_real_mul :
    forall a b : R,
      q866116_k_of_real (a * b) =
      q866116_k_mul (q866116_k_of_real a) (q866116_k_of_real b);
  q866116_k_of_real_neg :
    forall a : R,
      q866116_k_of_real (- a) =
      q866116_k_neg (q866116_k_of_real a);
  q866116_k_of_real_injective :
    forall a b : R,
      q866116_k_of_real a = q866116_k_of_real b ->
      a = b;
  q866116_k_norm_of_real :
    forall a : R,
      q866116_k_norm (q866116_k_of_real a) = Rabs a;

  q866116_k_re_of_real :
    forall a : R,
      q866116_k_re (q866116_k_of_real a) = a;
  q866116_k_im_of_real :
    forall a : R,
      q866116_k_im (q866116_k_of_real a) = 0;
  q866116_k_re_add :
    forall x y : K,
      q866116_k_re (q866116_k_add x y) =
      q866116_k_re x + q866116_k_re y;
  q866116_k_im_add :
    forall x y : K,
      q866116_k_im (q866116_k_add x y) =
      q866116_k_im x + q866116_k_im y;
  q866116_k_re_mul :
    forall x y : K,
      q866116_k_re (q866116_k_mul x y) =
      q866116_k_re x * q866116_k_re y -
      q866116_k_im x * q866116_k_im y;
  q866116_k_im_mul :
    forall x y : K,
      q866116_k_im (q866116_k_mul x y) =
      q866116_k_re x * q866116_k_im y +
      q866116_k_im x * q866116_k_re y;
  q866116_k_re_conj :
    forall x : K,
      q866116_k_re (q866116_k_conj x) = q866116_k_re x;
  q866116_k_im_conj :
    forall x : K,
      q866116_k_im (q866116_k_conj x) = - q866116_k_im x;
  q866116_k_re_I :
    q866116_k_re q866116_k_I = 0;
  q866116_k_im_I_real :
    q866116_k_I = q866116_k_zero ->
    q866116_k_im q866116_k_I = 0;
  q866116_k_im_I_complex :
    q866116_k_I <> q866116_k_zero ->
    q866116_k_im q866116_k_I = 1;
  q866116_k_I_cases :
    q866116_k_I = q866116_k_zero \/
    (q866116_k_I <> q866116_k_zero /\
     q866116_k_mul q866116_k_I q866116_k_I =
       q866116_k_neg q866116_k_one);
  q866116_k_coordinate_decomposition :
    forall x : K,
      x =
      q866116_k_add
        (q866116_k_of_real (q866116_k_re x))
        (q866116_k_mul
          (q866116_k_of_real (q866116_k_im x))
          q866116_k_I);
  q866116_k_norm_coordinates :
    forall x : K,
      q866116_k_norm x =
      sqrt (q866116_k_re x * q866116_k_re x +
            q866116_k_im x * q866116_k_im x)
}.

Arguments q866116_k_zero {K} _.
Arguments q866116_k_one {K} _.
Arguments q866116_k_add {K} _ _ _.
Arguments q866116_k_mul {K} _ _ _.
Arguments q866116_k_neg {K} _ _.
Arguments q866116_k_inv {K} _ _.
Arguments q866116_k_conj {K} _ _.
Arguments q866116_k_norm {K} _ _.
Arguments q866116_k_of_real {K} _ _.
Arguments q866116_k_re {K} _ _.
Arguments q866116_k_im {K} _ _.
Arguments q866116_k_I {K} _.

Record q866116_seminormed_space
    (K : Type) (F : q866116_rclike K) (E : Type) : Type := {
  q866116_e_zero : E;
  q866116_e_add : E -> E -> E;
  q866116_e_neg : E -> E;
  q866116_e_smul : K -> E -> E;
  q866116_e_norm : E -> R;

  q866116_e_add_assoc :
    forall x y z : E,
      q866116_e_add x (q866116_e_add y z) =
      q866116_e_add (q866116_e_add x y) z;
  q866116_e_add_comm :
    forall x y : E,
      q866116_e_add x y = q866116_e_add y x;
  q866116_e_add_zero :
    forall x : E,
      q866116_e_add x q866116_e_zero = x;
  q866116_e_add_neg :
    forall x : E,
      q866116_e_add x (q866116_e_neg x) = q866116_e_zero;

  q866116_e_one_smul :
    forall x : E,
      q866116_e_smul (q866116_k_one F) x = x;
  q866116_e_mul_smul :
    forall (a b : K) (x : E),
      q866116_e_smul (q866116_k_mul F a b) x =
      q866116_e_smul a (q866116_e_smul b x);
  q866116_e_add_smul :
    forall (a b : K) (x : E),
      q866116_e_smul (q866116_k_add F a b) x =
      q866116_e_add
        (q866116_e_smul a x) (q866116_e_smul b x);
  q866116_e_smul_add :
    forall (a : K) (x y : E),
      q866116_e_smul a (q866116_e_add x y) =
      q866116_e_add
        (q866116_e_smul a x) (q866116_e_smul a y);
  q866116_e_zero_smul :
    forall x : E,
      q866116_e_smul (q866116_k_zero F) x = q866116_e_zero;
  q866116_e_smul_zero :
    forall a : K,
      q866116_e_smul a q866116_e_zero = q866116_e_zero;

  q866116_e_norm_nonnegative :
    forall x : E,
      0 <= q866116_e_norm x;
  q866116_e_norm_zero :
    q866116_e_norm q866116_e_zero = 0;
  q866116_e_norm_neg :
    forall x : E,
      q866116_e_norm (q866116_e_neg x) = q866116_e_norm x;
  q866116_e_norm_add_le :
    forall x y : E,
      q866116_e_norm (q866116_e_add x y) <=
      q866116_e_norm x + q866116_e_norm y;
  q866116_e_norm_smul :
    forall (a : K) (x : E),
      q866116_e_norm (q866116_e_smul a x) =
      q866116_k_norm F a * q866116_e_norm x
}.

Arguments q866116_e_zero {K F E} _.
Arguments q866116_e_add {K F E} _ _ _.
Arguments q866116_e_neg {K F E} _ _.
Arguments q866116_e_smul {K F E} _ _ _.
Arguments q866116_e_norm {K F E} _ _.

Record q866116_subspace
    {K E : Type}
    {F : q866116_rclike K}
    (V : q866116_seminormed_space F E) : Type := {
  q866116_subspace_pred : E -> Prop;
  q866116_subspace_zero :
    q866116_subspace_pred (q866116_e_zero V);
  q866116_subspace_add :
    forall x y : E,
      q866116_subspace_pred x ->
      q866116_subspace_pred y ->
      q866116_subspace_pred (q866116_e_add V x y);
  q866116_subspace_smul :
    forall (a : K) (x : E),
      q866116_subspace_pred x ->
      q866116_subspace_pred (q866116_e_smul V a x)
}.

Arguments q866116_subspace_pred {K E F V} _ _.

Definition q866116_subspace_carrier
    {K E : Type}
    {F : q866116_rclike K}
    {V : q866116_seminormed_space F E}
    (P : q866116_subspace V) : Type :=
  {x : E | q866116_subspace_pred P x}.

Definition q866116_subspace_add_value
    {K E : Type}
    {F : q866116_rclike K}
    {V : q866116_seminormed_space F E}
    {P : q866116_subspace V}
    (x y : q866116_subspace_carrier P) :
    q866116_subspace_carrier P :=
  exist _ (q866116_e_add V (proj1_sig x) (proj1_sig y))
    (q866116_subspace_add P
      (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y)).

Definition q866116_subspace_smul_value
    {K E : Type}
    {F : q866116_rclike K}
    {V : q866116_seminormed_space F E}
    {P : q866116_subspace V}
    (a : K) (x : q866116_subspace_carrier P) :
    q866116_subspace_carrier P :=
  exist _ (q866116_e_smul V a (proj1_sig x))
    (q866116_subspace_smul P a (proj1_sig x) (proj2_sig x)).

Record q866116_continuous_linear_functional_on_subspace
    {K E : Type}
    {F : q866116_rclike K}
    {V : q866116_seminormed_space F E}
    (P : q866116_subspace V) : Type := {
  q866116_sub_apply : q866116_subspace_carrier P -> K;
  q866116_sub_map_add :
    forall x y : q866116_subspace_carrier P,
      q866116_sub_apply (q866116_subspace_add_value x y) =
      q866116_k_add F (q866116_sub_apply x) (q866116_sub_apply y);
  q866116_sub_map_smul :
    forall (a : K) (x : q866116_subspace_carrier P),
      q866116_sub_apply (q866116_subspace_smul_value a x) =
      q866116_k_mul F a (q866116_sub_apply x);
  q866116_sub_op_norm : R;
  q866116_sub_op_norm_nonnegative :
    0 <= q866116_sub_op_norm;
  q866116_sub_op_norm_bound :
    forall x : q866116_subspace_carrier P,
      q866116_k_norm F (q866116_sub_apply x) <=
      q866116_sub_op_norm * q866116_e_norm V (proj1_sig x);
  q866116_sub_op_norm_least :
    forall bound : R,
      0 <= bound ->
      (forall x : q866116_subspace_carrier P,
        q866116_k_norm F (q866116_sub_apply x) <=
        bound * q866116_e_norm V (proj1_sig x)) ->
      q866116_sub_op_norm <= bound
}.

Arguments q866116_sub_apply {K E F V P} _ _.
Arguments q866116_sub_op_norm {K E F V P} _.

Record q866116_continuous_linear_functional
    {K E : Type}
    {F : q866116_rclike K}
    (V : q866116_seminormed_space F E) : Type := {
  q866116_apply : E -> K;
  q866116_map_add :
    forall x y : E,
      q866116_apply (q866116_e_add V x y) =
      q866116_k_add F (q866116_apply x) (q866116_apply y);
  q866116_map_smul :
    forall (a : K) (x : E),
      q866116_apply (q866116_e_smul V a x) =
      q866116_k_mul F a (q866116_apply x);
  q866116_op_norm : R;
  q866116_op_norm_nonnegative :
    0 <= q866116_op_norm;
  q866116_op_norm_bound :
    forall x : E,
      q866116_k_norm F (q866116_apply x) <=
      q866116_op_norm * q866116_e_norm V x;
  q866116_op_norm_least :
    forall bound : R,
      0 <= bound ->
      (forall x : E,
        q866116_k_norm F (q866116_apply x) <=
        bound * q866116_e_norm V x) ->
      q866116_op_norm <= bound
}.

Arguments q866116_apply {K E F V} _ _.
Arguments q866116_op_norm {K E F V} _.

Theorem exists_extension_norm_eq :
  forall (K E : Type)
         (F : q866116_rclike K)
         (V : q866116_seminormed_space F E)
         (P : q866116_subspace V)
         (f : q866116_continuous_linear_functional_on_subspace P),
    exists g : q866116_continuous_linear_functional V,
      (forall x : q866116_subspace_carrier P,
        q866116_apply g (proj1_sig x) = q866116_sub_apply f x) /\
      q866116_op_norm g = q866116_sub_op_norm f.
Admitted.
