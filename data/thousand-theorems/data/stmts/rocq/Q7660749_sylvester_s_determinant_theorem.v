(*
  Statement-only formalization of Thousand Theorems corpus artifact Q7660749
  (thousand-theorems__rocq__Q7660749), "Sylvester's determinant theorem":
  over any commutative ring, rectangular matrices indexed by arbitrary finite
  types satisfy det(I + AB) = det(I + BA). This file contains no proof.
*)

From Stdlib Require Import List.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q7660749_commutative_ring (R : Type) : Type := {
  q7660749_zero : R;
  q7660749_one : R;
  q7660749_add : R -> R -> R;
  q7660749_mul : R -> R -> R;
  q7660749_neg : R -> R;
  q7660749_add_assoc :
    forall x y z : R,
      q7660749_add x (q7660749_add y z) =
      q7660749_add (q7660749_add x y) z;
  q7660749_add_comm :
    forall x y : R,
      q7660749_add x y = q7660749_add y x;
  q7660749_add_zero :
    forall x : R,
      q7660749_add x q7660749_zero = x;
  q7660749_add_neg :
    forall x : R,
      q7660749_add x (q7660749_neg x) = q7660749_zero;
  q7660749_mul_assoc :
    forall x y z : R,
      q7660749_mul x (q7660749_mul y z) =
      q7660749_mul (q7660749_mul x y) z;
  q7660749_mul_comm :
    forall x y : R,
      q7660749_mul x y = q7660749_mul y x;
  q7660749_mul_one :
    forall x : R,
      q7660749_mul x q7660749_one = x;
  q7660749_left_distrib :
    forall x y z : R,
      q7660749_mul x (q7660749_add y z) =
      q7660749_add
        (q7660749_mul x y)
        (q7660749_mul x z)
}.

Arguments q7660749_zero {R} _.
Arguments q7660749_one {R} _.
Arguments q7660749_add {R} _ _ _.
Arguments q7660749_mul {R} _ _ _.
Arguments q7660749_neg {R} _ _.

Record q7660749_finite_type (I : Type) : Type := {
  q7660749_enum : list I;
  q7660749_enum_nodup : NoDup q7660749_enum;
  q7660749_enum_complete :
    forall i : I, In i q7660749_enum;
  q7660749_eq_dec :
    forall i j : I, {i = j} + {i <> j}
}.

Arguments q7660749_enum {I} _.
Arguments q7660749_eq_dec {I} _ _ _.

Definition q7660749_matrix (I J R : Type) : Type :=
  I -> J -> R.

Fixpoint q7660749_sum_list {A R : Type}
    (ring : q7660749_commutative_ring R)
    (xs : list A)
    (f : A -> R) : R :=
  match xs with
  | [] => q7660749_zero ring
  | x :: rest =>
      q7660749_add ring
        (f x)
        (q7660749_sum_list ring rest f)
  end.

Definition q7660749_finite_sum {I R : Type}
    (ring : q7660749_commutative_ring R)
    (fin : q7660749_finite_type I)
    (f : I -> R) : R :=
  q7660749_sum_list ring (q7660749_enum fin) f.

Definition q7660749_identity_matrix {I R : Type}
    (ring : q7660749_commutative_ring R)
    (fin : q7660749_finite_type I) :
    q7660749_matrix I I R :=
  fun i j =>
    if q7660749_eq_dec fin i j
    then q7660749_one ring
    else q7660749_zero ring.

Definition q7660749_matrix_add {I J R : Type}
    (ring : q7660749_commutative_ring R)
    (A B : q7660749_matrix I J R) :
    q7660749_matrix I J R :=
  fun i j => q7660749_add ring (A i j) (B i j).

Definition q7660749_matrix_mul {I J K R : Type}
    (ring : q7660749_commutative_ring R)
    (fin : q7660749_finite_type J)
    (A : q7660749_matrix I J R)
    (B : q7660749_matrix J K R) :
    q7660749_matrix I K R :=
  fun i k =>
    q7660749_finite_sum ring fin
      (fun j => q7660749_mul ring (A i j) (B j k)).

Fixpoint q7660749_determinant_expansion {I R : Type}
    (ring : q7660749_commutative_ring R)
    (rows cols : list I)
    (M : q7660749_matrix I I R) {struct rows} : R :=
  match rows with
  | [] => q7660749_one ring
  | i :: remaining_rows =>
      let fix expand
          (prefix remaining_cols : list I)
          (positive : bool) {struct remaining_cols} : R :=
        match remaining_cols with
        | [] => q7660749_zero ring
        | j :: suffix =>
            let minor :=
              q7660749_determinant_expansion ring
                remaining_rows
                (rev prefix ++ suffix)
                M in
            let term := q7660749_mul ring (M i j) minor in
            q7660749_add ring
              (if positive then term else q7660749_neg ring term)
              (expand (j :: prefix) suffix (negb positive))
        end in
      expand [] cols true
  end.

Definition q7660749_determinant {I R : Type}
    (ring : q7660749_commutative_ring R)
    (fin : q7660749_finite_type I)
    (M : q7660749_matrix I I R) : R :=
  q7660749_determinant_expansion ring
    (q7660749_enum fin)
    (q7660749_enum fin)
    M.

Theorem Matrix_det_one_add_mul_comm :
  forall (R M N : Type)
         (ring : q7660749_commutative_ring R)
         (finM : q7660749_finite_type M)
         (finN : q7660749_finite_type N)
         (A : q7660749_matrix M N R)
         (B : q7660749_matrix N M R),
    q7660749_determinant ring finM
      (q7660749_matrix_add ring
        (q7660749_identity_matrix ring finM)
        (q7660749_matrix_mul ring finN A B)) =
    q7660749_determinant ring finN
      (q7660749_matrix_add ring
        (q7660749_identity_matrix ring finN)
        (q7660749_matrix_mul ring finM B A)).
Admitted.
