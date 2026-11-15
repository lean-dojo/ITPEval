(*
  Statement-only formalization of Thousand Theorems corpus artifact Q213603
  (thousand-theorems__rocq__Q213603), "Ceva's theorem": over an arbitrary
  normed field and normed affine torsor, three concurrent cevians of an
  affine-independent triangle have cyclic distance ratios whose product is
  one. This file contains no proof.
*)

From Stdlib Require Import Reals.

Set Universe Polymorphism.
Set Implicit Arguments.
Local Open Scope R_scope.

Record q213603_normed_field (K : Type) : Type := {
  q213603_kzero : K;
  q213603_kone : K;
  q213603_kadd : K -> K -> K;
  q213603_kmul : K -> K -> K;
  q213603_kneg : K -> K;
  q213603_kinv : K -> K;
  q213603_knorm : K -> R;

  q213603_kzero_ne_one :
    q213603_kzero <> q213603_kone;
  q213603_kadd_assoc :
    forall a b c : K,
      q213603_kadd a (q213603_kadd b c) =
      q213603_kadd (q213603_kadd a b) c;
  q213603_kadd_comm :
    forall a b : K,
      q213603_kadd a b = q213603_kadd b a;
  q213603_kadd_zero :
    forall a : K,
      q213603_kadd a q213603_kzero = a;
  q213603_kadd_neg :
    forall a : K,
      q213603_kadd a (q213603_kneg a) = q213603_kzero;
  q213603_kmul_assoc :
    forall a b c : K,
      q213603_kmul a (q213603_kmul b c) =
      q213603_kmul (q213603_kmul a b) c;
  q213603_kmul_comm :
    forall a b : K,
      q213603_kmul a b = q213603_kmul b a;
  q213603_kmul_one :
    forall a : K,
      q213603_kmul a q213603_kone = a;
  q213603_kleft_distrib :
    forall a b c : K,
      q213603_kmul a (q213603_kadd b c) =
      q213603_kadd
        (q213603_kmul a b) (q213603_kmul a c);
  q213603_kinv_zero :
    q213603_kinv q213603_kzero = q213603_kzero;
  q213603_kmul_inv :
    forall a : K,
      a <> q213603_kzero ->
      q213603_kmul a (q213603_kinv a) = q213603_kone;

  q213603_knorm_nonnegative :
    forall a : K,
      0 <= q213603_knorm a;
  q213603_knorm_eq_zero :
    forall a : K,
      q213603_knorm a = 0 <-> a = q213603_kzero;
  q213603_knorm_add_le :
    forall a b : K,
      q213603_knorm (q213603_kadd a b) <=
      q213603_knorm a + q213603_knorm b;
  q213603_knorm_mul :
    forall a b : K,
      q213603_knorm (q213603_kmul a b) =
      q213603_knorm a * q213603_knorm b;
  q213603_knorm_one :
    q213603_knorm q213603_kone = 1;
  q213603_knorm_neg :
    forall a : K,
      q213603_knorm (q213603_kneg a) = q213603_knorm a
}.

Arguments q213603_kzero {K} _.
Arguments q213603_kone {K} _.
Arguments q213603_kadd {K} _ _ _.
Arguments q213603_kmul {K} _ _ _.
Arguments q213603_kneg {K} _ _.
Arguments q213603_kinv {K} _ _.
Arguments q213603_knorm {K} _ _.

Record q213603_seminormed_space
    (K V : Type)
    (F : q213603_normed_field K) : Type := {
  q213603_vzero : V;
  q213603_vadd : V -> V -> V;
  q213603_vneg : V -> V;
  q213603_smul : K -> V -> V;
  q213603_vnorm : V -> R;

  q213603_vadd_assoc :
    forall x y z : V,
      q213603_vadd x (q213603_vadd y z) =
      q213603_vadd (q213603_vadd x y) z;
  q213603_vadd_comm :
    forall x y : V,
      q213603_vadd x y = q213603_vadd y x;
  q213603_vadd_zero :
    forall x : V,
      q213603_vadd x q213603_vzero = x;
  q213603_vadd_neg :
    forall x : V,
      q213603_vadd x (q213603_vneg x) = q213603_vzero;

  q213603_one_smul :
    forall x : V,
      q213603_smul (q213603_kone F) x = x;
  q213603_mul_smul :
    forall (a b : K) (x : V),
      q213603_smul (q213603_kmul F a b) x =
      q213603_smul a (q213603_smul b x);
  q213603_add_smul :
    forall (a b : K) (x : V),
      q213603_smul (q213603_kadd F a b) x =
      q213603_vadd
        (q213603_smul a x) (q213603_smul b x);
  q213603_smul_add :
    forall (a : K) (x y : V),
      q213603_smul a (q213603_vadd x y) =
      q213603_vadd
        (q213603_smul a x) (q213603_smul a y);
  q213603_zero_smul :
    forall x : V,
      q213603_smul (q213603_kzero F) x = q213603_vzero;
  q213603_smul_zero :
    forall a : K,
      q213603_smul a q213603_vzero = q213603_vzero;

  q213603_vnorm_nonnegative :
    forall x : V,
      0 <= q213603_vnorm x;
  q213603_vnorm_zero :
    q213603_vnorm q213603_vzero = 0;
  q213603_vnorm_neg :
    forall x : V,
      q213603_vnorm (q213603_vneg x) = q213603_vnorm x;
  q213603_vnorm_add_le :
    forall x y : V,
      q213603_vnorm (q213603_vadd x y) <=
      q213603_vnorm x + q213603_vnorm y;
  q213603_vnorm_smul :
    forall (a : K) (x : V),
      q213603_vnorm (q213603_smul a x) =
      q213603_knorm F a * q213603_vnorm x
}.

Arguments q213603_vzero {K V F} _.
Arguments q213603_vadd {K V F} _ _ _.
Arguments q213603_vneg {K V F} _ _.
Arguments q213603_smul {K V F} _ _ _.
Arguments q213603_vnorm {K V F} _ _.

Record q213603_normed_add_torsor
    (K V P : Type)
    (F : q213603_normed_field K)
    (S : @q213603_seminormed_space K V F) : Type := {
  q213603_vadd_point : V -> P -> P;
  q213603_vsub_point : P -> P -> V;
  q213603_zero_vadd :
    forall p : P,
      q213603_vadd_point (q213603_vzero S) p = p;
  q213603_add_vadd :
    forall (x y : V) (p : P),
      q213603_vadd_point (q213603_vadd S x y) p =
      q213603_vadd_point x (q213603_vadd_point y p);
  q213603_vsub_vadd :
    forall (x : V) (p : P),
      q213603_vsub_point (q213603_vadd_point x p) p = x;
  q213603_vadd_vsub :
    forall p q : P,
      q213603_vadd_point (q213603_vsub_point p q) q = p;
  q213603_dist_eq_zero_implies_eq :
    forall p q : P,
      q213603_vnorm S (q213603_vsub_point p q) = 0 ->
      p = q
}.

Arguments q213603_vadd_point {K V P F S} _ _ _.
Arguments q213603_vsub_point {K V P F S} _ _ _.

Definition q213603_dist
    {K V P : Type}
    {F : q213603_normed_field K}
    {S : @q213603_seminormed_space K V F}
    (A : @q213603_normed_add_torsor K V P F S)
    (p q : P) : R :=
  q213603_vnorm S (q213603_vsub_point A p q).

Definition q213603_mem_line
    {K V P : Type}
    {F : q213603_normed_field K}
    {S : @q213603_seminormed_space K V F}
    (A : @q213603_normed_add_torsor K V P F S)
    (a b x : P) : Prop :=
  exists r : K,
    x =
      q213603_vadd_point A
        (q213603_smul S r (q213603_vsub_point A b a)) a.

Definition q213603_affine_independent_triangle
    {K V P : Type}
    {F : q213603_normed_field K}
    {S : @q213603_seminormed_space K V F}
    (A : @q213603_normed_add_torsor K V P F S)
    (t0 t1 t2 : P) : Prop :=
  forall a b : K,
    q213603_vadd S
      (q213603_smul S a (q213603_vsub_point A t1 t0))
      (q213603_smul S b (q213603_vsub_point A t2 t0)) =
      q213603_vzero S ->
    a = q213603_kzero F /\ b = q213603_kzero F.

Theorem q213603_cevas_theorem :
  forall (K V P : Type)
         (F : q213603_normed_field K)
         (S : @q213603_seminormed_space K V F)
         (A : @q213603_normed_add_torsor K V P F S)
         (t0 t1 t2 p0 p1 p2 concurrent_point : P),
    q213603_affine_independent_triangle A t0 t1 t2 ->
    p0 <> t2 ->
    p1 <> t0 ->
    p2 <> t1 ->
    q213603_mem_line A t1 t2 p0 ->
    q213603_mem_line A t2 t0 p1 ->
    q213603_mem_line A t0 t1 p2 ->
    q213603_mem_line A t0 p0 concurrent_point ->
    q213603_mem_line A t1 p1 concurrent_point ->
    q213603_mem_line A t2 p2 concurrent_point ->
    (q213603_dist A t1 p0 / q213603_dist A p0 t2) *
      (q213603_dist A t2 p1 / q213603_dist A p1 t0) *
      (q213603_dist A t0 p2 / q213603_dist A p2 t1) = 1.
Admitted.
