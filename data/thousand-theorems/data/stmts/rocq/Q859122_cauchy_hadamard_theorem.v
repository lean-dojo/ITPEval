(*
  Statement-only formalization of Thousand Theorems corpus artifact Q859122
  (thousand-theorems__rocq__Q859122), "Cauchy–Hadamard theorem": for a
  formal multilinear series over arbitrary normed spaces, the inverse of its
  extended-nonnegative convergence radius is the limsup of the nth roots of
  its coefficient operator norms. This file contains no proof.
*)

From Stdlib Require Import Vectors.Fin Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q859122_nontrivially_normed_field (K : Type) : Type := {
  q859122_kzero : K;
  q859122_kone : K;
  q859122_kadd : K -> K -> K;
  q859122_kmul : K -> K -> K;
  q859122_kneg : K -> K;
  q859122_kinv : K -> K;
  q859122_knorm : K -> R;
  q859122_kzero_ne_one :
    q859122_kzero <> q859122_kone;
  q859122_kadd_assoc :
    forall a b c : K,
      q859122_kadd a (q859122_kadd b c) =
      q859122_kadd (q859122_kadd a b) c;
  q859122_kadd_comm :
    forall a b : K, q859122_kadd a b = q859122_kadd b a;
  q859122_kadd_zero :
    forall a : K, q859122_kadd a q859122_kzero = a;
  q859122_kadd_neg :
    forall a : K, q859122_kadd a (q859122_kneg a) = q859122_kzero;
  q859122_kmul_assoc :
    forall a b c : K,
      q859122_kmul a (q859122_kmul b c) =
      q859122_kmul (q859122_kmul a b) c;
  q859122_kmul_comm :
    forall a b : K, q859122_kmul a b = q859122_kmul b a;
  q859122_kmul_one :
    forall a : K, q859122_kmul a q859122_kone = a;
  q859122_kmul_inv :
    forall a : K,
      a <> q859122_kzero ->
      q859122_kmul a (q859122_kinv a) = q859122_kone;
  q859122_kinv_zero :
    q859122_kinv q859122_kzero = q859122_kzero;
  q859122_kmul_add :
    forall a b c : K,
      q859122_kmul a (q859122_kadd b c) =
      q859122_kadd (q859122_kmul a b) (q859122_kmul a c);
  q859122_knorm_nonnegative :
    forall a : K, 0 <= q859122_knorm a;
  q859122_knorm_eq_zero :
    forall a : K, q859122_knorm a = 0 <-> a = q859122_kzero;
  q859122_knorm_add_le :
    forall a b : K,
      q859122_knorm (q859122_kadd a b) <=
      q859122_knorm a + q859122_knorm b;
  q859122_knorm_mul :
    forall a b : K,
      q859122_knorm (q859122_kmul a b) =
      q859122_knorm a * q859122_knorm b;
  q859122_knorm_nontrivial :
    exists a : K, 1 < q859122_knorm a
}.

Arguments q859122_kzero {K} _.
Arguments q859122_kone {K} _.
Arguments q859122_kadd {K} _ _ _.
Arguments q859122_kmul {K} _ _ _.
Arguments q859122_kneg {K} _ _.
Arguments q859122_kinv {K} _ _.
Arguments q859122_knorm {K} _ _.

Record q859122_normed_add_comm_group (E : Type) : Type := {
  q859122_vzero : E;
  q859122_vadd : E -> E -> E;
  q859122_vneg : E -> E;
  q859122_vnorm : E -> R;
  q859122_vadd_assoc :
    forall x y z : E,
      q859122_vadd x (q859122_vadd y z) =
      q859122_vadd (q859122_vadd x y) z;
  q859122_vadd_comm :
    forall x y : E, q859122_vadd x y = q859122_vadd y x;
  q859122_vadd_zero :
    forall x : E, q859122_vadd x q859122_vzero = x;
  q859122_vadd_neg :
    forall x : E, q859122_vadd x (q859122_vneg x) = q859122_vzero;
  q859122_vnorm_nonnegative :
    forall x : E, 0 <= q859122_vnorm x;
  q859122_vnorm_eq_zero :
    forall x : E, q859122_vnorm x = 0 <-> x = q859122_vzero;
  q859122_vnorm_add_le :
    forall x y : E,
      q859122_vnorm (q859122_vadd x y) <=
      q859122_vnorm x + q859122_vnorm y;
  q859122_vnorm_neg :
    forall x : E, q859122_vnorm (q859122_vneg x) = q859122_vnorm x
}.

Arguments q859122_vzero {E} _.
Arguments q859122_vadd {E} _ _ _.
Arguments q859122_vneg {E} _ _.
Arguments q859122_vnorm {E} _ _.

Record q859122_normed_space
    (K E : Type)
    (KF : q859122_nontrivially_normed_field K)
    (NE : q859122_normed_add_comm_group E) : Type := {
  q859122_smul : K -> E -> E;
  q859122_one_smul :
    forall x : E, q859122_smul (q859122_kone KF) x = x;
  q859122_mul_smul :
    forall (a b : K) (x : E),
      q859122_smul (q859122_kmul KF a b) x =
      q859122_smul a (q859122_smul b x);
  q859122_add_smul :
    forall (a b : K) (x : E),
      q859122_smul (q859122_kadd KF a b) x =
      q859122_vadd NE (q859122_smul a x) (q859122_smul b x);
  q859122_smul_add :
    forall (a : K) (x y : E),
      q859122_smul a (q859122_vadd NE x y) =
      q859122_vadd NE (q859122_smul a x) (q859122_smul a y);
  q859122_zero_smul :
    forall x : E,
      q859122_smul (q859122_kzero KF) x = q859122_vzero NE;
  q859122_smul_zero :
    forall a : K,
      q859122_smul a (q859122_vzero NE) = q859122_vzero NE;
  q859122_norm_smul :
    forall (a : K) (x : E),
      q859122_vnorm NE (q859122_smul a x) =
      q859122_knorm KF a * q859122_vnorm NE x
}.

Arguments q859122_smul {K E KF NE} _ _ _.

Definition q859122_replace
    {A : Type} {n : nat}
    (x : Fin.t n -> A) (i : Fin.t n) (a : A) : Fin.t n -> A :=
  fun j =>
    if Fin.eq_dec j i then a else x j.

Fixpoint q859122_input_norm_product
    {E : Type}
    (NE : q859122_normed_add_comm_group E)
    (n : nat) : (Fin.t n -> E) -> R :=
  match n as k return (Fin.t k -> E) -> R with
  | O => fun _ => 1
  | S k =>
      fun x =>
        q859122_vnorm NE (x Fin.F1) *
        @q859122_input_norm_product E NE k
          (fun i : Fin.t k => x (Fin.FS i))
  end.

Record q859122_continuous_multilinear_map
    (K E F : Type)
    (KF : q859122_nontrivially_normed_field K)
    (NE : q859122_normed_add_comm_group E)
    (NF : q859122_normed_add_comm_group F)
    (VE : @q859122_normed_space K E KF NE)
    (VF : @q859122_normed_space K F KF NF)
    (n : nat) : Type := {
  q859122_map_apply : (Fin.t n -> E) -> F;
  q859122_map_add :
    forall (x : Fin.t n -> E) (i : Fin.t n) (a b : E),
      q859122_map_apply
        (q859122_replace x i (q859122_vadd NE a b)) =
      q859122_vadd NF
        (q859122_map_apply (q859122_replace x i a))
        (q859122_map_apply (q859122_replace x i b));
  q859122_map_smul :
    forall (x : Fin.t n -> E) (i : Fin.t n) (a : K) (v : E),
      q859122_map_apply
        (q859122_replace x i (q859122_smul VE a v)) =
      q859122_smul VF a
        (q859122_map_apply (q859122_replace x i v));
  q859122_operator_norm : R;
  q859122_operator_norm_nonnegative :
    0 <= q859122_operator_norm;
  q859122_le_operator_norm :
    forall x : Fin.t n -> E,
      q859122_vnorm NF (q859122_map_apply x) <=
      q859122_operator_norm *
      @q859122_input_norm_product E NE n x;
  q859122_operator_norm_least :
    forall C : R,
      0 <= C ->
      (forall x : Fin.t n -> E,
        q859122_vnorm NF (q859122_map_apply x) <=
        C * @q859122_input_norm_product E NE n x) ->
      q859122_operator_norm <= C
}.

Arguments q859122_map_apply
  {K E F KF NE NF VE VF n} _ _.
Arguments q859122_operator_norm
  {K E F KF NE NF VE VF n} _.
Arguments q859122_operator_norm_nonnegative
  {K E F KF NE NF VE VF n} _.

Definition q859122_formal_multilinear_series
    (K E F : Type)
    (KF : q859122_nontrivially_normed_field K)
    (NE : q859122_normed_add_comm_group E)
    (NF : q859122_normed_add_comm_group F)
    (VE : @q859122_normed_space K E KF NE)
    (VF : @q859122_normed_space K F KF NF) : Type :=
  forall n : nat,
    @q859122_continuous_multilinear_map K E F KF NE NF VE VF n.

Definition q859122_nnreal : Type :=
  {x : R | 0 <= x}.

Definition q859122_nnreal_value
    (x : q859122_nnreal) : R :=
  proj1_sig x.

Definition q859122_nnreal_zero : q859122_nnreal :=
  exist (fun x : R => 0 <= x) 0 (Rle_refl 0).

Definition q859122_nnreal_one : q859122_nnreal :=
  exist (fun x : R => 0 <= x) 1 Rle_0_1.

Definition q859122_nth_root
    (x : q859122_nnreal) (n : nat) : q859122_nnreal :=
  match n with
  | O => q859122_nnreal_one
  | S k =>
      if Req_EM_T (q859122_nnreal_value x) 0 then
        q859122_nnreal_zero
      else
        exist
          (fun y : R => 0 <= y)
          (exp
            (ln (q859122_nnreal_value x) /
             INR (S k)))
          (Rlt_le 0
            (exp
              (ln (q859122_nnreal_value x) /
               INR (S k)))
            (exp_pos
              (ln (q859122_nnreal_value x) /
               INR (S k))))
  end.

Inductive q859122_ennreal : Type :=
| q859122_ennreal_finite :
    q859122_nnreal -> q859122_ennreal
| q859122_ennreal_infinity :
    q859122_ennreal.

Definition q859122_ennreal_zero : q859122_ennreal :=
  q859122_ennreal_finite q859122_nnreal_zero.

Definition q859122_ennreal_eq
    (x y : q859122_ennreal) : Prop :=
  match x, y with
  | q859122_ennreal_finite a,
    q859122_ennreal_finite b =>
      q859122_nnreal_value a = q859122_nnreal_value b
  | q859122_ennreal_infinity,
    q859122_ennreal_infinity => True
  | _, _ => False
  end.

Definition q859122_ennreal_le
    (x y : q859122_ennreal) : Prop :=
  match x, y with
  | q859122_ennreal_finite a,
    q859122_ennreal_finite b =>
      q859122_nnreal_value a <= q859122_nnreal_value b
  | q859122_ennreal_finite _,
    q859122_ennreal_infinity => True
  | q859122_ennreal_infinity,
    q859122_ennreal_finite _ => False
  | q859122_ennreal_infinity,
    q859122_ennreal_infinity => True
  end.

Definition q859122_ennreal_inverse
    (x y : q859122_ennreal) : Prop :=
  match x with
  | q859122_ennreal_infinity =>
      q859122_ennreal_eq y q859122_ennreal_zero
  | q859122_ennreal_finite a =>
      if Req_EM_T (q859122_nnreal_value a) 0 then
        q859122_ennreal_eq y q859122_ennreal_infinity
      else
        match y with
        | q859122_ennreal_finite b =>
            q859122_nnreal_value b =
            / q859122_nnreal_value a
        | q859122_ennreal_infinity => False
        end
  end.

Definition q859122_is_supremum
    (S : q859122_ennreal -> Prop)
    (supremum : q859122_ennreal) : Prop :=
  (forall x : q859122_ennreal,
    S x -> q859122_ennreal_le x supremum) /\
  (forall upper : q859122_ennreal,
    (forall x : q859122_ennreal,
      S x -> q859122_ennreal_le x upper) ->
    q859122_ennreal_le supremum upper).

Definition q859122_is_infimum
    (S : q859122_ennreal -> Prop)
    (infimum : q859122_ennreal) : Prop :=
  (forall x : q859122_ennreal,
    S x -> q859122_ennreal_le infimum x) /\
  (forall lower : q859122_ennreal,
    (forall x : q859122_ennreal,
      S x -> q859122_ennreal_le lower x) ->
    q859122_ennreal_le lower infimum).

Definition q859122_coefficient_norm
    {K E F : Type}
    {KF : q859122_nontrivially_normed_field K}
    {NE : q859122_normed_add_comm_group E}
    {NF : q859122_normed_add_comm_group F}
    {VE : @q859122_normed_space K E KF NE}
    {VF : @q859122_normed_space K F KF NF}
    (p : @q859122_formal_multilinear_series K E F KF NE NF VE VF)
    (n : nat) : q859122_nnreal :=
  exist
    (fun x : R => 0 <= x)
    (q859122_operator_norm (p n))
    (q859122_operator_norm_nonnegative (p n)).

Definition q859122_radius_candidate
    {K E F : Type}
    {KF : q859122_nontrivially_normed_field K}
    {NE : q859122_normed_add_comm_group E}
    {NF : q859122_normed_add_comm_group F}
    {VE : @q859122_normed_space K E KF NE}
    {VF : @q859122_normed_space K F KF NF}
    (p : @q859122_formal_multilinear_series K E F KF NE NF VE VF)
    (r : q859122_nnreal) : Prop :=
  exists C : R,
    forall n : nat,
      q859122_nnreal_value (q859122_coefficient_norm p n) *
      (q859122_nnreal_value r) ^ n <= C.

Definition q859122_radius_is
    {K E F : Type}
    {KF : q859122_nontrivially_normed_field K}
    {NE : q859122_normed_add_comm_group E}
    {NF : q859122_normed_add_comm_group F}
    {VE : @q859122_normed_space K E KF NE}
    {VF : @q859122_normed_space K F KF NF}
    (p : @q859122_formal_multilinear_series K E F KF NE NF VE VF)
    (radius : q859122_ennreal) : Prop :=
  q859122_is_supremum
    (fun value : q859122_ennreal =>
      exists r : q859122_nnreal,
        q859122_ennreal_eq value
          (q859122_ennreal_finite r) /\
        q859122_radius_candidate p r)
    radius.

Definition q859122_root_norm_sequence
    {K E F : Type}
    {KF : q859122_nontrivially_normed_field K}
    {NE : q859122_normed_add_comm_group E}
    {NF : q859122_normed_add_comm_group F}
    {VE : @q859122_normed_space K E KF NE}
    {VF : @q859122_normed_space K F KF NF}
    (p : @q859122_formal_multilinear_series K E F KF NE NF VE VF)
    (n : nat) : q859122_ennreal :=
  q859122_ennreal_finite
    (q859122_nth_root (q859122_coefficient_norm p n) n).

Definition q859122_limsup_at_top_is
    (u : nat -> q859122_ennreal)
    (limit : q859122_ennreal) : Prop :=
  exists tail_supremum : nat -> q859122_ennreal,
    (forall N : nat,
      q859122_is_supremum
        (fun value : q859122_ennreal =>
          exists n : nat,
            (N <= n)%nat /\
            q859122_ennreal_eq value (u n))
        (tail_supremum N)) /\
    q859122_is_infimum
      (fun value : q859122_ennreal =>
        exists N : nat,
          q859122_ennreal_eq value (tail_supremum N))
      limit.

Theorem FormalMultilinearSeries_radius_inv_eq_limsup :
  forall
    (K E F : Type)
    (KF : q859122_nontrivially_normed_field K)
    (NE : q859122_normed_add_comm_group E)
    (NF : q859122_normed_add_comm_group F)
    (VE : @q859122_normed_space K E KF NE)
    (VF : @q859122_normed_space K F KF NF)
    (p : @q859122_formal_multilinear_series K E F KF NE NF VE VF)
    (radius limsup_value : q859122_ennreal),
    q859122_radius_is p radius ->
    q859122_limsup_at_top_is
      (q859122_root_norm_sequence p) limsup_value ->
    q859122_ennreal_inverse radius limsup_value.
Admitted.
