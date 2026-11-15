(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1426292
  (thousand-theorems__rocq__Q1426292), "Banach-Steinhaus theorem": pointwise
  bounded families of continuous semilinear maps from a complete seminormed
  space to a seminormed space are uniformly bounded. This file contains no
  proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q1426292_normed_field (K : Type) : Type := {
  q1426292_fzero : K;
  q1426292_fone : K;
  q1426292_fadd : K -> K -> K;
  q1426292_fmul : K -> K -> K;
  q1426292_fneg : K -> K;
  q1426292_finv : K -> K;
  q1426292_fadd_assoc :
    forall a b c : K,
      q1426292_fadd a (q1426292_fadd b c) =
      q1426292_fadd (q1426292_fadd a b) c;
  q1426292_fadd_comm :
    forall a b : K, q1426292_fadd a b = q1426292_fadd b a;
  q1426292_fadd_zero :
    forall a : K, q1426292_fadd a q1426292_fzero = a;
  q1426292_fadd_neg :
    forall a : K, q1426292_fadd a (q1426292_fneg a) = q1426292_fzero;
  q1426292_fmul_assoc :
    forall a b c : K,
      q1426292_fmul a (q1426292_fmul b c) =
      q1426292_fmul (q1426292_fmul a b) c;
  q1426292_fmul_comm :
    forall a b : K, q1426292_fmul a b = q1426292_fmul b a;
  q1426292_fmul_one :
    forall a : K, q1426292_fmul a q1426292_fone = a;
  q1426292_finv_zero :
    q1426292_finv q1426292_fzero = q1426292_fzero;
  q1426292_fmul_inv :
    forall a : K,
      a <> q1426292_fzero ->
      q1426292_fmul (q1426292_finv a) a = q1426292_fone;
  q1426292_fdistrib :
    forall a b c : K,
      q1426292_fmul a (q1426292_fadd b c) =
      q1426292_fadd
        (q1426292_fmul a b) (q1426292_fmul a c);
  q1426292_fzero_neq_one :
    q1426292_fzero <> q1426292_fone;
  q1426292_fnorm : K -> R;
  q1426292_fnorm_nonnegative :
    forall a : K, 0 <= q1426292_fnorm a;
  q1426292_fnorm_eq_zero :
    forall a : K,
      q1426292_fnorm a = 0 <-> a = q1426292_fzero;
  q1426292_fnorm_add :
    forall a b : K,
      q1426292_fnorm (q1426292_fadd a b) <=
      q1426292_fnorm a + q1426292_fnorm b;
  q1426292_fnorm_mul :
    forall a b : K,
      q1426292_fnorm (q1426292_fmul a b) =
      q1426292_fnorm a * q1426292_fnorm b;
  q1426292_fnorm_one :
    q1426292_fnorm q1426292_fone = 1;
  q1426292_norm_nontrivial :
    exists a : K, 1 < q1426292_fnorm a
}.

Arguments q1426292_fzero {K} _.
Arguments q1426292_fone {K} _.
Arguments q1426292_fadd {K} _ _ _.
Arguments q1426292_fmul {K} _ _ _.
Arguments q1426292_fneg {K} _ _.
Arguments q1426292_fnorm {K} _ _.

Record q1426292_seminormed_space
    (K E : Type) (scalar : q1426292_normed_field K) : Type := {
  q1426292_vzero : E;
  q1426292_vadd : E -> E -> E;
  q1426292_vneg : E -> E;
  q1426292_smul : K -> E -> E;
  q1426292_vadd_assoc :
    forall x y z : E,
      q1426292_vadd x (q1426292_vadd y z) =
      q1426292_vadd (q1426292_vadd x y) z;
  q1426292_vadd_comm :
    forall x y : E, q1426292_vadd x y = q1426292_vadd y x;
  q1426292_vadd_zero :
    forall x : E, q1426292_vadd x q1426292_vzero = x;
  q1426292_vadd_neg :
    forall x : E, q1426292_vadd x (q1426292_vneg x) = q1426292_vzero;
  q1426292_smul_one :
    forall x : E, q1426292_smul (q1426292_fone scalar) x = x;
  q1426292_smul_mul :
    forall (a b : K) (x : E),
      q1426292_smul (q1426292_fmul scalar a b) x =
      q1426292_smul a (q1426292_smul b x);
  q1426292_smul_add_scalar :
    forall (a b : K) (x : E),
      q1426292_smul (q1426292_fadd scalar a b) x =
      q1426292_vadd (q1426292_smul a x) (q1426292_smul b x);
  q1426292_smul_add_vector :
    forall (a : K) (x y : E),
      q1426292_smul a (q1426292_vadd x y) =
      q1426292_vadd (q1426292_smul a x) (q1426292_smul a y);
  q1426292_zero_smul :
    forall x : E,
      q1426292_smul (q1426292_fzero scalar) x = q1426292_vzero;
  q1426292_smul_zero :
    forall a : K,
      q1426292_smul a q1426292_vzero = q1426292_vzero;
  q1426292_vnorm : E -> R;
  q1426292_vnorm_nonnegative :
    forall x : E, 0 <= q1426292_vnorm x;
  q1426292_vnorm_zero :
    q1426292_vnorm q1426292_vzero = 0;
  q1426292_vnorm_neg :
    forall x : E, q1426292_vnorm (q1426292_vneg x) = q1426292_vnorm x;
  q1426292_vnorm_add :
    forall x y : E,
      q1426292_vnorm (q1426292_vadd x y) <=
      q1426292_vnorm x + q1426292_vnorm y;
  q1426292_vnorm_smul :
    forall (a : K) (x : E),
      q1426292_vnorm (q1426292_smul a x) =
      q1426292_fnorm scalar a * q1426292_vnorm x
}.

Arguments q1426292_vzero {K E scalar} _.
Arguments q1426292_vadd {K E scalar} _ _ _.
Arguments q1426292_vneg {K E scalar} _ _.
Arguments q1426292_smul {K E scalar} _ _ _.
Arguments q1426292_vnorm {K E scalar} _ _.

Definition q1426292_vsub
    {K E : Type}
    {scalar : q1426292_normed_field K}
    (space : @q1426292_seminormed_space K E scalar)
    (x y : E) : E :=
  q1426292_vadd space x (q1426292_vneg space y).

Record q1426292_isometric_ring_hom
    (K1 K2 : Type)
    (scalar1 : q1426292_normed_field K1)
    (scalar2 : q1426292_normed_field K2) : Type := {
  q1426292_ring_hom_fun : K1 -> K2;
  q1426292_ring_hom_zero :
    q1426292_ring_hom_fun (q1426292_fzero scalar1) =
    q1426292_fzero scalar2;
  q1426292_ring_hom_one :
    q1426292_ring_hom_fun (q1426292_fone scalar1) =
    q1426292_fone scalar2;
  q1426292_ring_hom_add :
    forall a b : K1,
      q1426292_ring_hom_fun (q1426292_fadd scalar1 a b) =
      q1426292_fadd scalar2
        (q1426292_ring_hom_fun a) (q1426292_ring_hom_fun b);
  q1426292_ring_hom_mul :
    forall a b : K1,
      q1426292_ring_hom_fun (q1426292_fmul scalar1 a b) =
      q1426292_fmul scalar2
        (q1426292_ring_hom_fun a) (q1426292_ring_hom_fun b);
  q1426292_ring_hom_isometric :
    forall a : K1,
      q1426292_fnorm scalar2 (q1426292_ring_hom_fun a) =
      q1426292_fnorm scalar1 a
}.

Arguments q1426292_ring_hom_fun
  {K1 K2 scalar1 scalar2} _ _.

Record q1426292_continuous_semilinear_map
    (K1 K2 E F : Type)
    (scalar1 : q1426292_normed_field K1)
    (scalar2 : q1426292_normed_field K2)
    (domain : @q1426292_seminormed_space K1 E scalar1)
    (codomain : @q1426292_seminormed_space K2 F scalar2)
    (sigma : @q1426292_isometric_ring_hom K1 K2 scalar1 scalar2) : Type := {
  q1426292_map_fun : E -> F;
  q1426292_map_add :
    forall x y : E,
      q1426292_map_fun (q1426292_vadd domain x y) =
      q1426292_vadd codomain
        (q1426292_map_fun x) (q1426292_map_fun y);
  q1426292_map_smul :
    forall (a : K1) (x : E),
      q1426292_map_fun (q1426292_smul domain a x) =
      q1426292_smul codomain
        (q1426292_ring_hom_fun sigma a) (q1426292_map_fun x);
  q1426292_map_op_norm : R;
  q1426292_map_op_norm_nonnegative :
    0 <= q1426292_map_op_norm;
  q1426292_map_op_norm_bound :
    forall x : E,
      q1426292_vnorm codomain (q1426292_map_fun x) <=
      q1426292_map_op_norm * q1426292_vnorm domain x;
  q1426292_map_op_norm_least :
    forall bound : R,
      0 <= bound ->
      (forall x : E,
        q1426292_vnorm codomain (q1426292_map_fun x) <=
        bound * q1426292_vnorm domain x) ->
      q1426292_map_op_norm <= bound
}.

Arguments q1426292_map_fun
  {K1 K2 E F scalar1 scalar2 domain codomain sigma} _ _.
Arguments q1426292_map_op_norm
  {K1 K2 E F scalar1 scalar2 domain codomain sigma} _.

Definition q1426292_cauchy_sequence
    {K E : Type}
    {scalar : q1426292_normed_field K}
    (space : @q1426292_seminormed_space K E scalar)
    (u : nat -> E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall m n : nat,
        (N <= m)%nat ->
        (N <= n)%nat ->
        q1426292_vnorm space
          (q1426292_vsub space (u m) (u n)) < epsilon.

Definition q1426292_sequence_converges
    {K E : Type}
    {scalar : q1426292_normed_field K}
    (space : @q1426292_seminormed_space K E scalar)
    (u : nat -> E)
    (limit : E) : Prop :=
  forall epsilon : R,
    0 < epsilon ->
    exists N : nat,
      forall n : nat,
        (N <= n)%nat ->
        q1426292_vnorm space
          (q1426292_vsub space (u n) limit) < epsilon.

Definition q1426292_complete_space
    {K E : Type}
    {scalar : q1426292_normed_field K}
    (space : @q1426292_seminormed_space K E scalar) : Prop :=
  forall u : nat -> E,
    q1426292_cauchy_sequence space u ->
    exists limit : E, q1426292_sequence_converges space u limit.

Theorem banach_steinhaus :
  forall (K1 K2 E F I : Type)
         (scalar1 : q1426292_normed_field K1)
         (scalar2 : q1426292_normed_field K2)
         (domain : @q1426292_seminormed_space K1 E scalar1)
         (codomain : @q1426292_seminormed_space K2 F scalar2)
         (sigma : @q1426292_isometric_ring_hom K1 K2 scalar1 scalar2)
         (g : I ->
           @q1426292_continuous_semilinear_map
             K1 K2 E F scalar1 scalar2 domain codomain sigma),
    q1426292_complete_space domain ->
    (forall x : E,
      exists pointwise_bound : R,
        forall i : I,
          q1426292_vnorm codomain
            (q1426292_map_fun (g i) x) <= pointwise_bound) ->
    exists uniform_bound : R,
      forall i : I,
        q1426292_map_op_norm (g i) <= uniform_bound.
Admitted.
