(*
  Statement-only formalization of Thousand Theorems corpus artifact Q17098298
  (thousand-theorems__rocq__Q17098298), "Jacobson density theorem": for a
  semisimple module, an endomorphism linear over its ring of linear
  endomorphisms agrees on every finite subset with multiplication by one
  scalar from the original ring. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q17098298_ring (R : Type) : Type := {
  q17098298_zero : R;
  q17098298_one : R;
  q17098298_add : R -> R -> R;
  q17098298_mul : R -> R -> R;
  q17098298_neg : R -> R;
  q17098298_add_assoc :
    forall x y z : R,
      q17098298_add x (q17098298_add y z) =
      q17098298_add (q17098298_add x y) z;
  q17098298_add_comm :
    forall x y : R,
      q17098298_add x y = q17098298_add y x;
  q17098298_zero_add :
    forall x : R, q17098298_add q17098298_zero x = x;
  q17098298_add_zero :
    forall x : R, q17098298_add x q17098298_zero = x;
  q17098298_neg_add :
    forall x : R,
      q17098298_add (q17098298_neg x) x = q17098298_zero;
  q17098298_add_neg :
    forall x : R,
      q17098298_add x (q17098298_neg x) = q17098298_zero;
  q17098298_mul_assoc :
    forall x y z : R,
      q17098298_mul x (q17098298_mul y z) =
      q17098298_mul (q17098298_mul x y) z;
  q17098298_one_mul :
    forall x : R, q17098298_mul q17098298_one x = x;
  q17098298_mul_one :
    forall x : R, q17098298_mul x q17098298_one = x;
  q17098298_mul_add :
    forall x y z : R,
      q17098298_mul x (q17098298_add y z) =
      q17098298_add
        (q17098298_mul x y) (q17098298_mul x z);
  q17098298_add_mul :
    forall x y z : R,
      q17098298_mul (q17098298_add x y) z =
      q17098298_add
        (q17098298_mul x z) (q17098298_mul y z);
  q17098298_zero_mul :
    forall x : R,
      q17098298_mul q17098298_zero x = q17098298_zero;
  q17098298_mul_zero :
    forall x : R,
      q17098298_mul x q17098298_zero = q17098298_zero
}.

Arguments q17098298_zero {R} _.
Arguments q17098298_one {R} _.
Arguments q17098298_add {R} _ _ _.
Arguments q17098298_mul {R} _ _ _.
Arguments q17098298_neg {R} _ _.

Record q17098298_module
    {R : Type}
    (A : q17098298_ring R)
    (M : Type) : Type := {
  q17098298_mzero : M;
  q17098298_madd : M -> M -> M;
  q17098298_mneg : M -> M;
  q17098298_smul : R -> M -> M;
  q17098298_madd_assoc :
    forall x y z : M,
      q17098298_madd x (q17098298_madd y z) =
      q17098298_madd (q17098298_madd x y) z;
  q17098298_madd_comm :
    forall x y : M,
      q17098298_madd x y = q17098298_madd y x;
  q17098298_mzero_add :
    forall x : M, q17098298_madd q17098298_mzero x = x;
  q17098298_madd_zero :
    forall x : M, q17098298_madd x q17098298_mzero = x;
  q17098298_mneg_add :
    forall x : M,
      q17098298_madd (q17098298_mneg x) x = q17098298_mzero;
  q17098298_madd_neg :
    forall x : M,
      q17098298_madd x (q17098298_mneg x) = q17098298_mzero;
  q17098298_one_smul :
    forall x : M,
      q17098298_smul (q17098298_one A) x = x;
  q17098298_mul_smul :
    forall (r s : R) (x : M),
      q17098298_smul (q17098298_mul A r s) x =
      q17098298_smul r (q17098298_smul s x);
  q17098298_add_smul :
    forall (r s : R) (x : M),
      q17098298_smul (q17098298_add A r s) x =
      q17098298_madd
        (q17098298_smul r x) (q17098298_smul s x);
  q17098298_smul_add :
    forall (r : R) (x y : M),
      q17098298_smul r (q17098298_madd x y) =
      q17098298_madd
        (q17098298_smul r x) (q17098298_smul r y);
  q17098298_zero_smul :
    forall x : M,
      q17098298_smul (q17098298_zero A) x = q17098298_mzero;
  q17098298_smul_zero :
    forall r : R,
      q17098298_smul r q17098298_mzero = q17098298_mzero
}.

Arguments q17098298_mzero {R A M} _.
Arguments q17098298_madd {R A M} _ _ _.
Arguments q17098298_mneg {R A M} _ _.
Arguments q17098298_smul {R A M} _ _ _.

Record q17098298_submodule
    {R M : Type}
    {A : q17098298_ring R}
    (V : q17098298_module A M) : Type := {
  q17098298_submodule_mem : M -> Prop;
  q17098298_submodule_zero :
    q17098298_submodule_mem (q17098298_mzero V);
  q17098298_submodule_add :
    forall x y : M,
      q17098298_submodule_mem x ->
      q17098298_submodule_mem y ->
      q17098298_submodule_mem (q17098298_madd V x y);
  q17098298_submodule_neg :
    forall x : M,
      q17098298_submodule_mem x ->
      q17098298_submodule_mem (q17098298_mneg V x);
  q17098298_submodule_smul :
    forall (r : R) (x : M),
      q17098298_submodule_mem x ->
      q17098298_submodule_mem (q17098298_smul V r x)
}.

Arguments q17098298_submodule_mem {R M A V} _ _.

Definition q17098298_are_complements
    {R M : Type}
    {A : q17098298_ring R}
    {V : q17098298_module A M}
    (N C : q17098298_submodule V) : Prop :=
  (forall x : M,
    q17098298_submodule_mem N x ->
    q17098298_submodule_mem C x ->
    x = q17098298_mzero V) /\
  (forall x : M,
    exists n c : M,
      q17098298_submodule_mem N n /\
      q17098298_submodule_mem C c /\
      x = q17098298_madd V n c).

Definition q17098298_is_semisimple_module
    {R M : Type}
    {A : q17098298_ring R}
    (V : q17098298_module A M) : Prop :=
  forall N : q17098298_submodule V,
    exists C : q17098298_submodule V,
      q17098298_are_complements N C.

Record q17098298_linear_endomorphism
    {R M : Type}
    {A : q17098298_ring R}
    (V : q17098298_module A M) : Type := {
  q17098298_linear_apply : M -> M;
  q17098298_linear_map_zero :
    q17098298_linear_apply (q17098298_mzero V) =
    q17098298_mzero V;
  q17098298_linear_map_add :
    forall x y : M,
      q17098298_linear_apply (q17098298_madd V x y) =
      q17098298_madd V
        (q17098298_linear_apply x)
        (q17098298_linear_apply y);
  q17098298_linear_map_smul :
    forall (r : R) (x : M),
      q17098298_linear_apply (q17098298_smul V r x) =
      q17098298_smul V r (q17098298_linear_apply x)
}.

Arguments q17098298_linear_apply {R M A V} _ _.

Record q17098298_end_linear_endomorphism
    {R M : Type}
    {A : q17098298_ring R}
    (V : q17098298_module A M) : Type := {
  q17098298_end_linear_apply : M -> M;
  q17098298_end_linear_map_zero :
    q17098298_end_linear_apply (q17098298_mzero V) =
    q17098298_mzero V;
  q17098298_end_linear_map_add :
    forall x y : M,
      q17098298_end_linear_apply (q17098298_madd V x y) =
      q17098298_madd V
        (q17098298_end_linear_apply x)
        (q17098298_end_linear_apply y);
  q17098298_end_linear_commutes :
    forall (g : q17098298_linear_endomorphism V) (x : M),
      q17098298_end_linear_apply (q17098298_linear_apply g x) =
      q17098298_linear_apply g (q17098298_end_linear_apply x)
}.

Arguments q17098298_end_linear_apply {R M A V} _ _.

Theorem jacobson_density :
  forall (R M : Type)
         (A : q17098298_ring R)
         (V : q17098298_module A M)
         (f : q17098298_end_linear_endomorphism V)
         (s : list M),
    q17098298_is_semisimple_module V ->
    exists r : R,
      forall m : M,
        In m s ->
        q17098298_end_linear_apply f m =
        q17098298_smul V r m.
Admitted.
