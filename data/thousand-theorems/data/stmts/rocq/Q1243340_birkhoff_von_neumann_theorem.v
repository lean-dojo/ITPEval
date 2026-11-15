(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1243340
  (thousand-theorems__rocq__Q1243340), "Birkhoff–Von Neumann theorem": over
  any linear ordered field and finite index type, the doubly stochastic
  matrices are exactly the convex hull of the permutation matrices. This
  file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1243340_linear_ordered_field (F : Type) : Type := {
  q1243340_zero : F;
  q1243340_one : F;
  q1243340_add : F -> F -> F;
  q1243340_mul : F -> F -> F;
  q1243340_neg : F -> F;
  q1243340_inv : F -> F;
  q1243340_le : F -> F -> Prop;
  q1243340_zero_ne_one :
    q1243340_zero <> q1243340_one;
  q1243340_add_assoc :
    forall x y z : F,
      q1243340_add x (q1243340_add y z) =
      q1243340_add (q1243340_add x y) z;
  q1243340_add_comm :
    forall x y : F,
      q1243340_add x y = q1243340_add y x;
  q1243340_add_zero :
    forall x : F, q1243340_add x q1243340_zero = x;
  q1243340_add_neg :
    forall x : F,
      q1243340_add x (q1243340_neg x) = q1243340_zero;
  q1243340_mul_assoc :
    forall x y z : F,
      q1243340_mul x (q1243340_mul y z) =
      q1243340_mul (q1243340_mul x y) z;
  q1243340_mul_comm :
    forall x y : F,
      q1243340_mul x y = q1243340_mul y x;
  q1243340_mul_one :
    forall x : F, q1243340_mul x q1243340_one = x;
  q1243340_left_distrib :
    forall x y z : F,
      q1243340_mul x (q1243340_add y z) =
      q1243340_add
        (q1243340_mul x y) (q1243340_mul x z);
  q1243340_inv_zero :
    q1243340_inv q1243340_zero = q1243340_zero;
  q1243340_mul_inv :
    forall x : F,
      x <> q1243340_zero ->
      q1243340_mul x (q1243340_inv x) = q1243340_one;
  q1243340_le_refl :
    forall x : F, q1243340_le x x;
  q1243340_le_trans :
    forall x y z : F,
      q1243340_le x y ->
      q1243340_le y z ->
      q1243340_le x z;
  q1243340_le_antisym :
    forall x y : F,
      q1243340_le x y ->
      q1243340_le y x ->
      x = y;
  q1243340_le_total :
    forall x y : F,
      q1243340_le x y \/ q1243340_le y x;
  q1243340_add_le_add_left :
    forall x y z : F,
      q1243340_le x y ->
      q1243340_le
        (q1243340_add z x) (q1243340_add z y);
  q1243340_mul_pos :
    forall x y : F,
      q1243340_le q1243340_zero x ->
      q1243340_le q1243340_zero y ->
      q1243340_le q1243340_zero (q1243340_mul x y)
}.

Arguments q1243340_zero {F} _.
Arguments q1243340_one {F} _.
Arguments q1243340_add {F} _ _ _.
Arguments q1243340_mul {F} _ _ _.
Arguments q1243340_neg {F} _ _.
Arguments q1243340_inv {F} _ _.
Arguments q1243340_le {F} _ _ _.

Record q1243340_finite_type (I : Type) : Type := {
  q1243340_enum : list I;
  q1243340_enum_nodup : NoDup q1243340_enum;
  q1243340_enum_complete :
    forall i : I, In i q1243340_enum;
  q1243340_eq_dec :
    forall i j : I, {i = j} + {i <> j}
}.

Arguments q1243340_enum {I} _.
Arguments q1243340_eq_dec {I} _ _ _.

Record q1243340_permutation (I : Type) : Type := {
  q1243340_perm_apply : I -> I;
  q1243340_perm_inverse : I -> I;
  q1243340_perm_left_inverse :
    forall i : I,
      q1243340_perm_inverse (q1243340_perm_apply i) = i;
  q1243340_perm_right_inverse :
    forall i : I,
      q1243340_perm_apply (q1243340_perm_inverse i) = i
}.

Arguments q1243340_perm_apply {I} _ _.
Arguments q1243340_perm_inverse {I} _ _.

Definition q1243340_set (A : Type) : Type := A -> Prop.

Definition q1243340_subset {A : Type}
    (S T : q1243340_set A) : Prop :=
  forall x : A, S x -> T x.

Definition q1243340_same_set {A : Type}
    (S T : q1243340_set A) : Prop :=
  forall x : A, S x <-> T x.

Definition q1243340_matrix (I F : Type) : Type :=
  I -> I -> F.

Definition q1243340_matrix_equal {I F : Type}
    (A B : q1243340_matrix I F) : Prop :=
  forall i j : I, A i j = B i j.

(* Matrix predicates are extensional, as they are in the Lean source. *)
Definition q1243340_matrix_extensional {I F : Type}
    (S : q1243340_set (q1243340_matrix I F)) : Prop :=
  forall A B : q1243340_matrix I F,
    q1243340_matrix_equal A B ->
    S A ->
    S B.

Fixpoint q1243340_sum_list {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (xs : list I)
    (f : I -> F) : F :=
  match xs with
  | nil => q1243340_zero fld
  | cons x rest =>
      q1243340_add fld
        (f x) (q1243340_sum_list fld rest f)
  end.

Definition q1243340_finite_sum {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (fin : q1243340_finite_type I)
    (f : I -> F) : F :=
  q1243340_sum_list fld (q1243340_enum fin) f.

Definition q1243340_matrix_add {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (A B : q1243340_matrix I F) : q1243340_matrix I F :=
  fun i j =>
    q1243340_add fld (A i j) (B i j).

Definition q1243340_matrix_smul {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (a : F)
    (A : q1243340_matrix I F) : q1243340_matrix I F :=
  fun i j => q1243340_mul fld a (A i j).

Definition q1243340_convex {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (S : q1243340_set (q1243340_matrix I F)) : Prop :=
  forall (A B : q1243340_matrix I F) (a b : F),
    S A ->
    S B ->
    q1243340_le fld (q1243340_zero fld) a ->
    q1243340_le fld (q1243340_zero fld) b ->
    q1243340_add fld a b = q1243340_one fld ->
    S
      (q1243340_matrix_add fld
        (q1243340_matrix_smul fld a A)
        (q1243340_matrix_smul fld b B)).

Definition q1243340_convex_hull {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (S : q1243340_set (q1243340_matrix I F))
    : q1243340_set (q1243340_matrix I F) :=
  fun M =>
    forall C : q1243340_set (q1243340_matrix I F),
      q1243340_matrix_extensional C ->
      q1243340_convex fld C ->
      q1243340_subset S C ->
      C M.

Definition q1243340_permutation_matrix {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (fin : q1243340_finite_type I)
    (p : q1243340_permutation I) : q1243340_matrix I F :=
  fun i j =>
    if q1243340_eq_dec fin (q1243340_perm_apply p i) j
    then q1243340_one fld
    else q1243340_zero fld.

Definition q1243340_permutation_matrices {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (fin : q1243340_finite_type I)
    : q1243340_set (q1243340_matrix I F) :=
  fun M =>
    exists p : q1243340_permutation I,
      q1243340_matrix_equal M
        (q1243340_permutation_matrix fld fin p).

Definition q1243340_doubly_stochastic {I F : Type}
    (fld : q1243340_linear_ordered_field F)
    (fin : q1243340_finite_type I)
    (M : q1243340_matrix I F) : Prop :=
  (forall i j : I,
    q1243340_le fld (q1243340_zero fld) (M i j)) /\
  (forall i : I,
    q1243340_finite_sum fld fin (fun j => M i j) =
    q1243340_one fld) /\
  forall j : I,
    q1243340_finite_sum fld fin (fun i => M i j) =
    q1243340_one fld.

Theorem doublyStochastic_eq_convexHull_permMatrix :
  forall (F I : Type)
         (fld : q1243340_linear_ordered_field F)
         (fin : q1243340_finite_type I),
    q1243340_same_set
      (q1243340_doubly_stochastic fld fin)
      (q1243340_convex_hull fld
        (q1243340_permutation_matrices fld fin)).
Admitted.
