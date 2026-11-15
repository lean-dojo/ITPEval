(*
  Statement-only formalization of Thousand Theorems corpus artifact Q656198
  (thousand-theorems__rocq__Q656198), "Maschke's theorem": over a field, if
  the cardinality of a finite group is nonzero in the field, every submodule
  of a module over the group algebra has a complementary submodule.
  This file contains no proof.
*)

From Stdlib Require Import Lists.List.

Set Universe Polymorphism.
Set Primitive Projections.
Set Implicit Arguments.

Record q656198_field (K : Type) : Type := {
  q656198_fzero : K;
  q656198_fone : K;
  q656198_fadd : K -> K -> K;
  q656198_fmul : K -> K -> K;
  q656198_fneg : K -> K;
  q656198_finv : K -> K;
  q656198_fadd_assoc :
    forall x y z : K,
      q656198_fadd x (q656198_fadd y z) =
      q656198_fadd (q656198_fadd x y) z;
  q656198_fadd_comm :
    forall x y : K,
      q656198_fadd x y = q656198_fadd y x;
  q656198_fzero_add :
    forall x : K, q656198_fadd q656198_fzero x = x;
  q656198_fadd_zero :
    forall x : K, q656198_fadd x q656198_fzero = x;
  q656198_fneg_add :
    forall x : K,
      q656198_fadd (q656198_fneg x) x = q656198_fzero;
  q656198_fadd_neg :
    forall x : K,
      q656198_fadd x (q656198_fneg x) = q656198_fzero;
  q656198_fmul_assoc :
    forall x y z : K,
      q656198_fmul x (q656198_fmul y z) =
      q656198_fmul (q656198_fmul x y) z;
  q656198_fmul_comm :
    forall x y : K,
      q656198_fmul x y = q656198_fmul y x;
  q656198_fone_mul :
    forall x : K, q656198_fmul q656198_fone x = x;
  q656198_fmul_one :
    forall x : K, q656198_fmul x q656198_fone = x;
  q656198_fmul_add :
    forall x y z : K,
      q656198_fmul x (q656198_fadd y z) =
      q656198_fadd
        (q656198_fmul x y) (q656198_fmul x z);
  q656198_fadd_mul :
    forall x y z : K,
      q656198_fmul (q656198_fadd x y) z =
      q656198_fadd
        (q656198_fmul x z) (q656198_fmul y z);
  q656198_fzero_mul :
    forall x : K,
      q656198_fmul q656198_fzero x = q656198_fzero;
  q656198_fmul_zero :
    forall x : K,
      q656198_fmul x q656198_fzero = q656198_fzero;
  q656198_fzero_ne_one :
    q656198_fzero <> q656198_fone;
  q656198_finv_zero :
    q656198_finv q656198_fzero = q656198_fzero;
  q656198_finv_mul :
    forall x : K,
      x <> q656198_fzero ->
      q656198_fmul (q656198_finv x) x = q656198_fone;
  q656198_fmul_inv :
    forall x : K,
      x <> q656198_fzero ->
      q656198_fmul x (q656198_finv x) = q656198_fone
}.

Arguments q656198_fzero {K} _.
Arguments q656198_fone {K} _.
Arguments q656198_fadd {K} _ _ _.
Arguments q656198_fmul {K} _ _ _.
Arguments q656198_fneg {K} _ _.
Arguments q656198_finv {K} _ _.

Fixpoint q656198_nat_cast
    {K : Type}
    (F : q656198_field K)
    (n : nat) : K :=
  match n with
  | O => q656198_fzero F
  | S m => q656198_fadd F (q656198_nat_cast F m) (q656198_fone F)
  end.

Record q656198_group (G : Type) : Type := {
  q656198_gone : G;
  q656198_gmul : G -> G -> G;
  q656198_ginv : G -> G;
  q656198_gmul_assoc :
    forall x y z : G,
      q656198_gmul x (q656198_gmul y z) =
      q656198_gmul (q656198_gmul x y) z;
  q656198_gone_mul :
    forall x : G, q656198_gmul q656198_gone x = x;
  q656198_gmul_one :
    forall x : G, q656198_gmul x q656198_gone = x;
  q656198_ginv_mul :
    forall x : G,
      q656198_gmul (q656198_ginv x) x = q656198_gone;
  q656198_gmul_inv :
    forall x : G,
      q656198_gmul x (q656198_ginv x) = q656198_gone
}.

Arguments q656198_gone {G} _.
Arguments q656198_gmul {G} _ _ _.
Arguments q656198_ginv {G} _ _.

Record q656198_finite_type (G : Type) : Type := {
  q656198_eq_dec :
    forall x y : G, {x = y} + {x <> y};
  q656198_enum : list G;
  q656198_enum_nodup :
    List.NoDup q656198_enum;
  q656198_enum_complete :
    forall x : G, List.In x q656198_enum
}.

Arguments q656198_eq_dec {G} _ _ _.
Arguments q656198_enum {G} _.

Definition q656198_group_algebra
    (K G : Type) : Type :=
  G -> K.

Definition q656198_ga_zero
    {K G : Type}
    (F : q656198_field K) :
    q656198_group_algebra K G :=
  fun _ => q656198_fzero F.

Definition q656198_ga_one
    {K G : Type}
    (F : q656198_field K)
    (T : q656198_finite_type G)
    (H : q656198_group G) :
    q656198_group_algebra K G :=
  fun x =>
    if q656198_eq_dec T x (q656198_gone H)
    then q656198_fone F
    else q656198_fzero F.

Definition q656198_ga_add
    {K G : Type}
    (F : q656198_field K)
    (u v : q656198_group_algebra K G) :
    q656198_group_algebra K G :=
  fun x => q656198_fadd F (u x) (v x).

Definition q656198_ga_neg
    {K G : Type}
    (F : q656198_field K)
    (u : q656198_group_algebra K G) :
    q656198_group_algebra K G :=
  fun x => q656198_fneg F (u x).

Fixpoint q656198_sum
    {K G : Type}
    (F : q656198_field K)
    (xs : list G)
    (term : G -> K) : K :=
  match xs with
  | nil => q656198_fzero F
  | cons x rest =>
      q656198_fadd F (term x) (q656198_sum F rest term)
  end.

Definition q656198_ga_mul
    {K G : Type}
    (F : q656198_field K)
    (T : q656198_finite_type G)
    (H : q656198_group G)
    (u v : q656198_group_algebra K G) :
    q656198_group_algebra K G :=
  fun x =>
    q656198_sum F (q656198_enum T)
      (fun a =>
        q656198_fmul F
          (u a)
          (v (q656198_gmul H (q656198_ginv H a) x))).

Record q656198_module
    (K G V : Type)
    (F : q656198_field K)
    (T : q656198_finite_type G)
    (H : q656198_group G) : Type := {
  q656198_mzero : V;
  q656198_madd : V -> V -> V;
  q656198_mneg : V -> V;
  q656198_smul :
    q656198_group_algebra K G -> V -> V;
  q656198_madd_assoc :
    forall x y z : V,
      q656198_madd x (q656198_madd y z) =
      q656198_madd (q656198_madd x y) z;
  q656198_madd_comm :
    forall x y : V,
      q656198_madd x y = q656198_madd y x;
  q656198_mzero_add :
    forall x : V, q656198_madd q656198_mzero x = x;
  q656198_madd_zero :
    forall x : V, q656198_madd x q656198_mzero = x;
  q656198_mneg_add :
    forall x : V,
      q656198_madd (q656198_mneg x) x = q656198_mzero;
  q656198_madd_neg :
    forall x : V,
      q656198_madd x (q656198_mneg x) = q656198_mzero;
  q656198_one_smul :
    forall x : V,
      q656198_smul (q656198_ga_one F T H) x = x;
  q656198_mul_smul :
    forall (a b : q656198_group_algebra K G) (x : V),
      q656198_smul (q656198_ga_mul F T H a b) x =
      q656198_smul a (q656198_smul b x);
  q656198_add_smul :
    forall (a b : q656198_group_algebra K G) (x : V),
      q656198_smul (q656198_ga_add F a b) x =
      q656198_madd (q656198_smul a x) (q656198_smul b x);
  q656198_smul_add :
    forall (a : q656198_group_algebra K G) (x y : V),
      q656198_smul a (q656198_madd x y) =
      q656198_madd (q656198_smul a x) (q656198_smul a y);
  q656198_zero_smul :
    forall x : V,
      q656198_smul (q656198_ga_zero F) x = q656198_mzero;
  q656198_smul_zero :
    forall a : q656198_group_algebra K G,
      q656198_smul a q656198_mzero = q656198_mzero
}.

Arguments q656198_module (K G V) F T H : clear implicits.
Arguments q656198_mzero {K G V F T H} _.
Arguments q656198_madd {K G V F T H} _ _ _.
Arguments q656198_mneg {K G V F T H} _ _.
Arguments q656198_smul {K G V F T H} _ _ _.

Record q656198_submodule
    {K G V : Type}
    {F : q656198_field K}
    {T : q656198_finite_type G}
    {H : q656198_group G}
    (M : q656198_module K G V F T H) : Type := {
  q656198_submodule_mem : V -> Prop;
  q656198_submodule_zero :
    q656198_submodule_mem (q656198_mzero M);
  q656198_submodule_add :
    forall x y : V,
      q656198_submodule_mem x ->
      q656198_submodule_mem y ->
      q656198_submodule_mem (q656198_madd M x y);
  q656198_submodule_neg :
    forall x : V,
      q656198_submodule_mem x ->
      q656198_submodule_mem (q656198_mneg M x);
  q656198_submodule_smul :
    forall (a : q656198_group_algebra K G) (x : V),
      q656198_submodule_mem x ->
      q656198_submodule_mem (q656198_smul M a x)
}.

Arguments q656198_submodule_mem {K G V F T H M} _ _.

Definition q656198_are_complements
    {K G V : Type}
    {F : q656198_field K}
    {T : q656198_finite_type G}
    {H : q656198_group G}
    {M : q656198_module K G V F T H}
    (P Q : q656198_submodule M) : Prop :=
  (forall x : V,
    q656198_submodule_mem P x ->
    q656198_submodule_mem Q x ->
    x = q656198_mzero M) /\
  (forall x : V,
    exists p q : V,
      q656198_submodule_mem P p /\
      q656198_submodule_mem Q q /\
      x = q656198_madd M p q).

Theorem MonoidAlgebra_Submodule_exists_isCompl :
  forall (K G V : Type)
         (F : q656198_field K)
         (T : q656198_finite_type G)
         (H : q656198_group G)
         (M : q656198_module K G V F T H)
         (P : q656198_submodule M),
    q656198_nat_cast F (List.length (q656198_enum T)) <>
      q656198_fzero F ->
    exists Q : q656198_submodule M,
      q656198_are_complements P Q.
Admitted.
