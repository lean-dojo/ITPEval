(*
  Statement-only formalization of Thousand Theorems corpus artifact Q944297
  (thousand-theorems__rocq__Q944297), "Open mapping theorem (functional
  analysis)": a surjective continuous semilinear map between Banach spaces
  over isometrically equivalent nontrivially normed fields is an open map.
  This file contains no proof.
*)

From Stdlib Require Import Reals Arith.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q944297_normed_field (K : Type) : Type := {
  q944297_nf_zero : K;
  q944297_nf_one : K;
  q944297_nf_add : K -> K -> K;
  q944297_nf_mul : K -> K -> K;
  q944297_nf_neg : K -> K;
  q944297_nf_inv : K -> K;
  q944297_nf_add_assoc :
    forall x y z : K,
      q944297_nf_add x (q944297_nf_add y z) =
      q944297_nf_add (q944297_nf_add x y) z;
  q944297_nf_add_comm :
    forall x y : K, q944297_nf_add x y = q944297_nf_add y x;
  q944297_nf_add_zero :
    forall x : K, q944297_nf_add x q944297_nf_zero = x;
  q944297_nf_add_neg :
    forall x : K,
      q944297_nf_add x (q944297_nf_neg x) = q944297_nf_zero;
  q944297_nf_mul_assoc :
    forall x y z : K,
      q944297_nf_mul x (q944297_nf_mul y z) =
      q944297_nf_mul (q944297_nf_mul x y) z;
  q944297_nf_mul_comm :
    forall x y : K, q944297_nf_mul x y = q944297_nf_mul y x;
  q944297_nf_mul_one :
    forall x : K, q944297_nf_mul x q944297_nf_one = x;
  q944297_nf_left_distrib :
    forall x y z : K,
      q944297_nf_mul x (q944297_nf_add y z) =
      q944297_nf_add
        (q944297_nf_mul x y) (q944297_nf_mul x z);
  q944297_nf_inv_zero :
    q944297_nf_inv q944297_nf_zero = q944297_nf_zero;
  q944297_nf_mul_inv :
    forall x : K, x <> q944297_nf_zero ->
      q944297_nf_mul x (q944297_nf_inv x) = q944297_nf_one;
  q944297_nf_nontrivial :
    q944297_nf_zero <> q944297_nf_one;
  q944297_nf_norm : K -> R;
  q944297_nf_norm_nonnegative :
    forall x : K, 0 <= q944297_nf_norm x;
  q944297_nf_norm_eq_zero :
    forall x : K,
      q944297_nf_norm x = 0 <-> x = q944297_nf_zero;
  q944297_nf_norm_add_le :
    forall x y : K,
      q944297_nf_norm (q944297_nf_add x y) <=
      q944297_nf_norm x + q944297_nf_norm y;
  q944297_nf_norm_mul :
    forall x y : K,
      q944297_nf_norm (q944297_nf_mul x y) =
      q944297_nf_norm x * q944297_nf_norm y;
  q944297_nf_norm_nontrivial :
    exists x : K, 1 < q944297_nf_norm x
}.

Arguments q944297_nf_zero {K} _.
Arguments q944297_nf_one {K} _.
Arguments q944297_nf_add {K} _ _ _.
Arguments q944297_nf_mul {K} _ _ _.
Arguments q944297_nf_neg {K} _ _.
Arguments q944297_nf_inv {K} _ _.
Arguments q944297_nf_norm {K} _ _.

Record q944297_isometric_ring_equiv
    (K K' : Type)
    (scalar : q944297_normed_field K)
    (scalar' : q944297_normed_field K') : Type := {
  q944297_to_fun : K -> K';
  q944297_from_fun : K' -> K;
  q944297_to_zero :
    q944297_to_fun (q944297_nf_zero scalar) =
    q944297_nf_zero scalar';
  q944297_to_one :
    q944297_to_fun (q944297_nf_one scalar) =
    q944297_nf_one scalar';
  q944297_to_add :
    forall x y : K,
      q944297_to_fun (q944297_nf_add scalar x y) =
      q944297_nf_add scalar' (q944297_to_fun x) (q944297_to_fun y);
  q944297_to_mul :
    forall x y : K,
      q944297_to_fun (q944297_nf_mul scalar x y) =
      q944297_nf_mul scalar' (q944297_to_fun x) (q944297_to_fun y);
  q944297_from_zero :
    q944297_from_fun (q944297_nf_zero scalar') =
    q944297_nf_zero scalar;
  q944297_from_one :
    q944297_from_fun (q944297_nf_one scalar') =
    q944297_nf_one scalar;
  q944297_from_add :
    forall x y : K',
      q944297_from_fun (q944297_nf_add scalar' x y) =
      q944297_nf_add scalar (q944297_from_fun x) (q944297_from_fun y);
  q944297_from_mul :
    forall x y : K',
      q944297_from_fun (q944297_nf_mul scalar' x y) =
      q944297_nf_mul scalar (q944297_from_fun x) (q944297_from_fun y);
  q944297_from_to :
    forall x : K, q944297_from_fun (q944297_to_fun x) = x;
  q944297_to_from :
    forall y : K', q944297_to_fun (q944297_from_fun y) = y;
  q944297_to_isometric :
    forall x : K,
      q944297_nf_norm scalar' (q944297_to_fun x) =
      q944297_nf_norm scalar x;
  q944297_from_isometric :
    forall y : K',
      q944297_nf_norm scalar (q944297_from_fun y) =
      q944297_nf_norm scalar' y
}.

Arguments q944297_to_fun {K K' scalar scalar'} _ _.
Arguments q944297_from_fun {K K' scalar scalar'} _ _.

Record q944297_normed_vector_space
    (K : Type)
    (scalar : q944297_normed_field K)
    (E : Type) : Type := {
  q944297_nv_zero : E;
  q944297_nv_add : E -> E -> E;
  q944297_nv_neg : E -> E;
  q944297_nv_smul : K -> E -> E;
  q944297_nv_norm : E -> R;
  q944297_nv_add_assoc :
    forall x y z : E,
      q944297_nv_add x (q944297_nv_add y z) =
      q944297_nv_add (q944297_nv_add x y) z;
  q944297_nv_add_comm :
    forall x y : E, q944297_nv_add x y = q944297_nv_add y x;
  q944297_nv_add_zero :
    forall x : E, q944297_nv_add x q944297_nv_zero = x;
  q944297_nv_add_neg :
    forall x : E,
      q944297_nv_add x (q944297_nv_neg x) = q944297_nv_zero;
  q944297_nv_one_smul :
    forall x : E,
      q944297_nv_smul (q944297_nf_one scalar) x = x;
  q944297_nv_mul_smul :
    forall (a b : K) (x : E),
      q944297_nv_smul (q944297_nf_mul scalar a b) x =
      q944297_nv_smul a (q944297_nv_smul b x);
  q944297_nv_add_smul :
    forall (a b : K) (x : E),
      q944297_nv_smul (q944297_nf_add scalar a b) x =
      q944297_nv_add
        (q944297_nv_smul a x) (q944297_nv_smul b x);
  q944297_nv_smul_add :
    forall (a : K) (x y : E),
      q944297_nv_smul a (q944297_nv_add x y) =
      q944297_nv_add
        (q944297_nv_smul a x) (q944297_nv_smul a y);
  q944297_nv_zero_smul :
    forall x : E,
      q944297_nv_smul (q944297_nf_zero scalar) x = q944297_nv_zero;
  q944297_nv_smul_zero :
    forall a : K,
      q944297_nv_smul a q944297_nv_zero = q944297_nv_zero;
  q944297_nv_norm_nonnegative :
    forall x : E, 0 <= q944297_nv_norm x;
  q944297_nv_norm_eq_zero :
    forall x : E,
      q944297_nv_norm x = 0 <-> x = q944297_nv_zero;
  q944297_nv_norm_add_le :
    forall x y : E,
      q944297_nv_norm (q944297_nv_add x y) <=
      q944297_nv_norm x + q944297_nv_norm y;
  q944297_nv_norm_smul :
    forall (a : K) (x : E),
      q944297_nv_norm (q944297_nv_smul a x) =
      q944297_nf_norm scalar a * q944297_nv_norm x
}.

Arguments q944297_nv_zero {K scalar E} _.
Arguments q944297_nv_add {K scalar E} _ _ _.
Arguments q944297_nv_neg {K scalar E} _ _.
Arguments q944297_nv_smul {K scalar E} _ _ _.
Arguments q944297_nv_norm {K scalar E} _ _.

Definition q944297_sub
    {K E : Type}
    {scalar : q944297_normed_field K}
    (space : @q944297_normed_vector_space K scalar E)
    (x y : E) : E :=
  q944297_nv_add space x (q944297_nv_neg space y).

Definition q944297_dist
    {K E : Type}
    {scalar : q944297_normed_field K}
    (space : @q944297_normed_vector_space K scalar E)
    (x y : E) : R :=
  q944297_nv_norm space (q944297_sub space x y).

Definition q944297_sequence_cauchy
    {K E : Type}
    {scalar : q944297_normed_field K}
    (space : @q944297_normed_vector_space K scalar E)
    (u : nat -> E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall m n : nat,
      (N <= m)%nat ->
      (N <= n)%nat ->
      q944297_dist space (u m) (u n) < epsilon.

Definition q944297_sequence_converges
    {K E : Type}
    {scalar : q944297_normed_field K}
    (space : @q944297_normed_vector_space K scalar E)
    (u : nat -> E) (limit : E) : Prop :=
  forall epsilon : R, 0 < epsilon ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      q944297_dist space (u n) limit < epsilon.

Definition q944297_complete
    {K E : Type}
    {scalar : q944297_normed_field K}
    (space : @q944297_normed_vector_space K scalar E) : Prop :=
  forall u : nat -> E,
    q944297_sequence_cauchy space u ->
    exists limit : E, q944297_sequence_converges space u limit.

Definition q944297_metric_open
    {K E : Type}
    {scalar : q944297_normed_field K}
    (space : @q944297_normed_vector_space K scalar E)
    (U : E -> Prop) : Prop :=
  forall x : E, U x ->
    exists radius : R, 0 < radius /\
      forall y : E, q944297_dist space y x < radius -> U y.

Record q944297_continuous_semilinear_map
    (K K' E F : Type)
    (scalar : q944297_normed_field K)
    (scalar' : q944297_normed_field K')
    (domain : @q944297_normed_vector_space K scalar E)
    (codomain : @q944297_normed_vector_space K' scalar' F)
    (sigma : q944297_isometric_ring_equiv scalar scalar') : Type := {
  q944297_map_fun : E -> F;
  q944297_map_add :
    forall x y : E,
      q944297_map_fun (q944297_nv_add domain x y) =
      q944297_nv_add codomain (q944297_map_fun x) (q944297_map_fun y);
  q944297_map_smul :
    forall (a : K) (x : E),
      q944297_map_fun (q944297_nv_smul domain a x) =
      q944297_nv_smul codomain
        (q944297_to_fun sigma a) (q944297_map_fun x);
  q944297_map_continuous :
    forall x : E, forall epsilon : R, 0 < epsilon ->
      exists delta : R, 0 < delta /\
        forall y : E,
          q944297_dist domain y x < delta ->
          q944297_dist codomain
            (q944297_map_fun y) (q944297_map_fun x) < epsilon
}.

Arguments q944297_map_fun
  {K K' E F scalar scalar' domain codomain sigma} _ _.

Definition q944297_is_open_map
    {K K' E F : Type}
    {scalar : q944297_normed_field K}
    {scalar' : q944297_normed_field K'}
    {domain : @q944297_normed_vector_space K scalar E}
    {codomain : @q944297_normed_vector_space K' scalar' F}
    {sigma : q944297_isometric_ring_equiv scalar scalar'}
    (f : @q944297_continuous_semilinear_map
      K K' E F scalar scalar' domain codomain sigma) : Prop :=
  forall U : E -> Prop,
    q944297_metric_open domain U ->
    q944297_metric_open codomain
      (fun y : F =>
        exists x : E, U x /\ q944297_map_fun f x = y).

Theorem ContinuousLinearMap_isOpenMap :
  forall (K K' E F : Type)
         (scalar : q944297_normed_field K)
         (scalar' : q944297_normed_field K')
         (domain : @q944297_normed_vector_space K scalar E)
         (codomain : @q944297_normed_vector_space K' scalar' F)
         (sigma : q944297_isometric_ring_equiv scalar scalar')
         (f : @q944297_continuous_semilinear_map
           K K' E F scalar scalar' domain codomain sigma),
    q944297_complete domain ->
    q944297_complete codomain ->
    (forall y : F, exists x : E, q944297_map_fun f x = y) ->
    q944297_is_open_map f.
Admitted.
