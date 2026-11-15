(*
  Statement-only formalization of Thousand Theorems corpus artifact Q656772
  (thousand-theorems__rocq__Q656772), "Cayley–Hamilton theorem": over any
  commutative ring, evaluating the characteristic polynomial of a square
  matrix indexed by an arbitrary finite type at the matrix itself gives the
  zero matrix. This file contains no proof.
*)

From Stdlib Require Import List.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q656772_commutative_ring (R : Type) : Type := {
  q656772_zero : R;
  q656772_one : R;
  q656772_add : R -> R -> R;
  q656772_mul : R -> R -> R;
  q656772_neg : R -> R;
  q656772_add_assoc :
    forall x y z : R,
      q656772_add x (q656772_add y z) =
      q656772_add (q656772_add x y) z;
  q656772_add_comm :
    forall x y : R,
      q656772_add x y = q656772_add y x;
  q656772_add_zero :
    forall x : R,
      q656772_add x q656772_zero = x;
  q656772_add_neg :
    forall x : R,
      q656772_add x (q656772_neg x) = q656772_zero;
  q656772_mul_assoc :
    forall x y z : R,
      q656772_mul x (q656772_mul y z) =
      q656772_mul (q656772_mul x y) z;
  q656772_mul_comm :
    forall x y : R,
      q656772_mul x y = q656772_mul y x;
  q656772_mul_one :
    forall x : R,
      q656772_mul x q656772_one = x;
  q656772_left_distrib :
    forall x y z : R,
      q656772_mul x (q656772_add y z) =
      q656772_add
        (q656772_mul x y)
        (q656772_mul x z)
}.

Arguments q656772_zero {R} _.
Arguments q656772_one {R} _.
Arguments q656772_add {R} _ _ _.
Arguments q656772_mul {R} _ _ _.
Arguments q656772_neg {R} _ _.

Record q656772_finite_type (I : Type) : Type := {
  q656772_enum : list I;
  q656772_enum_nodup : NoDup q656772_enum;
  q656772_enum_complete :
    forall i : I, In i q656772_enum;
  q656772_eq_dec :
    forall i j : I, {i = j} + {i <> j}
}.

Arguments q656772_enum {I} _.
Arguments q656772_eq_dec {I} _ _ _.

Definition q656772_matrix (I R : Type) : Type :=
  I -> I -> R.

Definition q656772_matrix_equal {I R : Type}
    (A B : q656772_matrix I R) : Prop :=
  forall i j : I, A i j = B i j.

Fixpoint q656772_sum_list {A R : Type}
    (ring : q656772_commutative_ring R)
    (xs : list A)
    (f : A -> R) : R :=
  match xs with
  | [] => q656772_zero ring
  | x :: rest =>
      q656772_add ring
        (f x)
        (q656772_sum_list ring rest f)
  end.

Definition q656772_finite_sum {I R : Type}
    (ring : q656772_commutative_ring R)
    (fin : q656772_finite_type I)
    (f : I -> R) : R :=
  q656772_sum_list ring (q656772_enum fin) f.

Definition q656772_zero_matrix {I R : Type}
    (ring : q656772_commutative_ring R) :
    q656772_matrix I R :=
  fun _ _ => q656772_zero ring.

Definition q656772_scalar_matrix {I R : Type}
    (ring : q656772_commutative_ring R)
    (fin : q656772_finite_type I)
    (a : R) : q656772_matrix I R :=
  fun i j =>
    if q656772_eq_dec fin i j
    then a
    else q656772_zero ring.

Definition q656772_matrix_add {I R : Type}
    (ring : q656772_commutative_ring R)
    (A B : q656772_matrix I R) :
    q656772_matrix I R :=
  fun i j => q656772_add ring (A i j) (B i j).

Definition q656772_matrix_mul {I R : Type}
    (ring : q656772_commutative_ring R)
    (fin : q656772_finite_type I)
    (A B : q656772_matrix I R) :
    q656772_matrix I R :=
  fun i j =>
    q656772_finite_sum ring fin
      (fun k => q656772_mul ring (A i k) (B k j)).

Definition q656772_polynomial (R : Type) : Type :=
  list R.

Definition q656772_poly_zero {R : Type} :
    q656772_polynomial R :=
  [].

Definition q656772_poly_one {R : Type}
    (ring : q656772_commutative_ring R) :
    q656772_polynomial R :=
  [q656772_one ring].

Definition q656772_poly_constant {R : Type}
    (a : R) : q656772_polynomial R :=
  [a].

Definition q656772_poly_X {R : Type}
    (ring : q656772_commutative_ring R) :
    q656772_polynomial R :=
  [q656772_zero ring; q656772_one ring].

Fixpoint q656772_poly_add {R : Type}
    (ring : q656772_commutative_ring R)
    (p q : q656772_polynomial R) :
    q656772_polynomial R :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' =>
      q656772_add ring a b ::
      q656772_poly_add ring p' q'
  end.

Fixpoint q656772_poly_neg {R : Type}
    (ring : q656772_commutative_ring R)
    (p : q656772_polynomial R) :
    q656772_polynomial R :=
  match p with
  | [] => []
  | a :: rest =>
      q656772_neg ring a ::
      q656772_poly_neg ring rest
  end.

Definition q656772_poly_sub {R : Type}
    (ring : q656772_commutative_ring R)
    (p q : q656772_polynomial R) :
    q656772_polynomial R :=
  q656772_poly_add ring p (q656772_poly_neg ring q).

Fixpoint q656772_poly_scale {R : Type}
    (ring : q656772_commutative_ring R)
    (a : R)
    (p : q656772_polynomial R) :
    q656772_polynomial R :=
  match p with
  | [] => []
  | b :: rest =>
      q656772_mul ring a b ::
      q656772_poly_scale ring a rest
  end.

Fixpoint q656772_poly_mul {R : Type}
    (ring : q656772_commutative_ring R)
    (p q : q656772_polynomial R) :
    q656772_polynomial R :=
  match p with
  | [] => []
  | a :: rest =>
      q656772_poly_add ring
        (q656772_poly_scale ring a q)
        (q656772_zero ring ::
          q656772_poly_mul ring rest q)
  end.

Fixpoint q656772_determinant {I A : Type}
    (zero one : A)
    (add mul : A -> A -> A)
    (neg : A -> A)
    (rows cols : list I)
    (M : I -> I -> A) {struct rows} : A :=
  match rows with
  | [] => one
  | i :: remaining_rows =>
      let fix expand
          (prefix remaining_cols : list I)
          (positive : bool) {struct remaining_cols} : A :=
        match remaining_cols with
        | [] => zero
        | j :: suffix =>
            let minor :=
              q656772_determinant
                zero one add mul neg
                remaining_rows
                (rev prefix ++ suffix)
                M in
            let term := mul (M i j) minor in
            add
              (if positive then term else neg term)
              (expand (j :: prefix) suffix (negb positive))
        end in
      expand [] cols true
  end.

Definition q656772_charmatrix_entry {I R : Type}
    (ring : q656772_commutative_ring R)
    (fin : q656772_finite_type I)
    (M : q656772_matrix I R)
    (i j : I) : q656772_polynomial R :=
  q656772_poly_sub ring
    (if q656772_eq_dec fin i j
     then q656772_poly_X ring
     else q656772_poly_zero)
    (q656772_poly_constant (M i j)).

Definition q656772_charpoly {I R : Type}
    (ring : q656772_commutative_ring R)
    (fin : q656772_finite_type I)
    (M : q656772_matrix I R) :
    q656772_polynomial R :=
  q656772_determinant
    q656772_poly_zero
    (q656772_poly_one ring)
    (q656772_poly_add ring)
    (q656772_poly_mul ring)
    (q656772_poly_neg ring)
    (q656772_enum fin)
    (q656772_enum fin)
    (q656772_charmatrix_entry ring fin M).

Fixpoint q656772_aeval_matrix {I R : Type}
    (ring : q656772_commutative_ring R)
    (fin : q656772_finite_type I)
    (M : q656772_matrix I R)
    (p : q656772_polynomial R) :
    q656772_matrix I R :=
  match p with
  | [] => q656772_zero_matrix ring
  | a :: rest =>
      q656772_matrix_add ring
        (q656772_scalar_matrix ring fin a)
        (q656772_matrix_mul ring fin M
          (q656772_aeval_matrix ring fin M rest))
  end.

Theorem Matrix_aeval_self_charpoly :
  forall (R I : Type)
         (ring : q656772_commutative_ring R)
         (fin : q656772_finite_type I)
         (M : q656772_matrix I R),
    q656772_matrix_equal
      (q656772_aeval_matrix ring fin M
        (q656772_charpoly ring fin M))
      (q656772_zero_matrix ring).
Admitted.
