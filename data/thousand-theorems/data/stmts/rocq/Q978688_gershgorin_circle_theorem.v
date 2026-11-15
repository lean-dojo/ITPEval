(*
  Statement-only formalization of Thousand Theorems corpus artifact Q978688
  (thousand-theorems__rocq__Q978688), "Gershgorin circle theorem": every
  eigenvalue of a square matrix over a normed field lies in a closed ball
  centered at some diagonal entry, with radius the sum of the norms of the
  off-diagonal entries in that row. This file contains no proof.
*)

From Stdlib Require Import Lists.List Reals.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q978688_normed_field (K : Type) : Type := {
  q978688_zero : K;
  q978688_one : K;
  q978688_add : K -> K -> K;
  q978688_mul : K -> K -> K;
  q978688_neg : K -> K;
  q978688_inv : K -> K;
  q978688_add_assoc :
    forall x y z : K,
      q978688_add x (q978688_add y z) =
      q978688_add (q978688_add x y) z;
  q978688_add_comm :
    forall x y : K, q978688_add x y = q978688_add y x;
  q978688_add_zero :
    forall x : K, q978688_add x q978688_zero = x;
  q978688_add_neg :
    forall x : K, q978688_add x (q978688_neg x) = q978688_zero;
  q978688_mul_assoc :
    forall x y z : K,
      q978688_mul x (q978688_mul y z) =
      q978688_mul (q978688_mul x y) z;
  q978688_mul_comm :
    forall x y : K, q978688_mul x y = q978688_mul y x;
  q978688_mul_one :
    forall x : K, q978688_mul x q978688_one = x;
  q978688_left_distrib :
    forall x y z : K,
      q978688_mul x (q978688_add y z) =
      q978688_add (q978688_mul x y) (q978688_mul x z);
  q978688_zero_ne_one :
    q978688_zero <> q978688_one;
  q978688_inv_zero :
    q978688_inv q978688_zero = q978688_zero;
  q978688_mul_inv :
    forall x : K, x <> q978688_zero ->
      q978688_mul x (q978688_inv x) = q978688_one;
  q978688_norm : K -> R;
  q978688_norm_nonnegative :
    forall x : K, Rle 0 (q978688_norm x);
  q978688_norm_eq_zero :
    forall x : K,
      q978688_norm x = 0%R <-> x = q978688_zero;
  q978688_norm_neg :
    forall x : K,
      q978688_norm (q978688_neg x) = q978688_norm x;
  q978688_norm_add_le :
    forall x y : K,
      Rle (q978688_norm (q978688_add x y))
          (Rplus (q978688_norm x) (q978688_norm y));
  q978688_norm_mul :
    forall x y : K,
      q978688_norm (q978688_mul x y) =
      Rmult (q978688_norm x) (q978688_norm y)
}.

Arguments q978688_zero {K} _.
Arguments q978688_one {K} _.
Arguments q978688_add {K} _ _ _.
Arguments q978688_mul {K} _ _ _.
Arguments q978688_neg {K} _ _.
Arguments q978688_inv {K} _ _.
Arguments q978688_norm {K} _ _.

Record q978688_finite_type (I : Type) : Type := {
  q978688_enum : list I;
  q978688_enum_nodup : NoDup q978688_enum;
  q978688_enum_complete :
    forall i : I, In i q978688_enum;
  q978688_eq_dec :
    forall i j : I, {i = j} + {i <> j}
}.

Arguments q978688_enum {I} _.
Arguments q978688_eq_dec {I} _ _ _.

Definition q978688_matrix (I K : Type) : Type :=
  I -> I -> K.

Fixpoint q978688_sum_field_list {I K : Type}
    (field : q978688_normed_field K)
    (indices : list I)
    (f : I -> K) : K :=
  match indices with
  | nil => q978688_zero field
  | i :: rest =>
      q978688_add field
        (f i)
        (q978688_sum_field_list field rest f)
  end.

Definition q978688_mul_vec {I K : Type}
    (field : q978688_normed_field K)
    (finite : q978688_finite_type I)
    (A : q978688_matrix I K)
    (v : I -> K)
    (i : I) : K :=
  q978688_sum_field_list field (q978688_enum finite)
    (fun j => q978688_mul field (A i j) (v j)).

Definition q978688_has_eigenvalue {I K : Type}
    (field : q978688_normed_field K)
    (finite : q978688_finite_type I)
    (A : q978688_matrix I K)
    (mu : K) : Prop :=
  exists v : I -> K,
    (exists i : I, v i <> q978688_zero field) /\
    forall i : I,
      q978688_mul_vec field finite A v i =
      q978688_mul field mu (v i).

Fixpoint q978688_sum_off_diagonal {I K : Type}
    (field : q978688_normed_field K)
    (finite : q978688_finite_type I)
    (A : q978688_matrix I K)
    (row : I)
    (indices : list I) : R :=
  match indices with
  | nil => 0%R
  | j :: rest =>
      if q978688_eq_dec finite j row
      then q978688_sum_off_diagonal field finite A row rest
      else Rplus
        (q978688_norm field (A row j))
        (q978688_sum_off_diagonal field finite A row rest)
  end.

Definition q978688_row_radius {I K : Type}
    (field : q978688_normed_field K)
    (finite : q978688_finite_type I)
    (A : q978688_matrix I K)
    (row : I) : R :=
  q978688_sum_off_diagonal field finite A row
    (q978688_enum finite).

Definition q978688_in_closed_ball {K : Type}
    (field : q978688_normed_field K)
    (center point : K)
    (radius : R) : Prop :=
  Rle
    (q978688_norm field
      (q978688_add field point (q978688_neg field center)))
    radius.

Theorem eigenvalue_mem_ball :
  forall (K I : Type)
         (field : q978688_normed_field K)
         (finite : q978688_finite_type I)
         (A : q978688_matrix I K)
         (mu : K),
    q978688_has_eigenvalue field finite A mu ->
    exists k : I,
      q978688_in_closed_ball field (A k k) mu
        (q978688_row_radius field finite A k).
Admitted.
