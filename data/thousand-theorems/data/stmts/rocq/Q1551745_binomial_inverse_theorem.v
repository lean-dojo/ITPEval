(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1551745
  (thousand-theorems__rocq__Q1551745), "Binomial inverse theorem": over an
  arbitrary ring, compatible finite rectangular matrices satisfy the binomial
  inverse identity under the three required two-sided invertibility
  assumptions. This file contains no proof.
*)

From Stdlib Require Import List.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q1551745_ring (R : Type) : Type := {
  q1551745_zero : R;
  q1551745_one : R;
  q1551745_add : R -> R -> R;
  q1551745_mul : R -> R -> R;
  q1551745_neg : R -> R;
  q1551745_add_assoc :
    forall x y z : R,
      q1551745_add x (q1551745_add y z) =
      q1551745_add (q1551745_add x y) z;
  q1551745_add_comm :
    forall x y : R,
      q1551745_add x y = q1551745_add y x;
  q1551745_zero_add :
    forall x : R,
      q1551745_add q1551745_zero x = x;
  q1551745_add_zero :
    forall x : R,
      q1551745_add x q1551745_zero = x;
  q1551745_neg_add :
    forall x : R,
      q1551745_add (q1551745_neg x) x = q1551745_zero;
  q1551745_add_neg :
    forall x : R,
      q1551745_add x (q1551745_neg x) = q1551745_zero;
  q1551745_mul_assoc :
    forall x y z : R,
      q1551745_mul x (q1551745_mul y z) =
      q1551745_mul (q1551745_mul x y) z;
  q1551745_one_mul :
    forall x : R,
      q1551745_mul q1551745_one x = x;
  q1551745_mul_one :
    forall x : R,
      q1551745_mul x q1551745_one = x;
  q1551745_mul_add :
    forall x y z : R,
      q1551745_mul x (q1551745_add y z) =
      q1551745_add
        (q1551745_mul x y)
        (q1551745_mul x z);
  q1551745_add_mul :
    forall x y z : R,
      q1551745_mul (q1551745_add x y) z =
      q1551745_add
        (q1551745_mul x z)
        (q1551745_mul y z);
  q1551745_zero_mul :
    forall x : R,
      q1551745_mul q1551745_zero x = q1551745_zero;
  q1551745_mul_zero :
    forall x : R,
      q1551745_mul x q1551745_zero = q1551745_zero
}.

Arguments q1551745_zero {R} _.
Arguments q1551745_one {R} _.
Arguments q1551745_add {R} _ _ _.
Arguments q1551745_mul {R} _ _ _.
Arguments q1551745_neg {R} _ _.

Record q1551745_finite_type (I : Type) : Type := {
  q1551745_enum : list I;
  q1551745_enum_nodup : NoDup q1551745_enum;
  q1551745_enum_complete :
    forall i : I, In i q1551745_enum;
  q1551745_eq_dec :
    forall i j : I, {i = j} + {i <> j}
}.

Arguments q1551745_enum {I} _.
Arguments q1551745_eq_dec {I} _ _ _.

Definition q1551745_matrix (I J R : Type) : Type :=
  I -> J -> R.

Definition q1551745_matrix_equal {I J R : Type}
    (A B : q1551745_matrix I J R) : Prop :=
  forall i j, A i j = B i j.

Fixpoint q1551745_sum_list {I R : Type}
    (ring : q1551745_ring R)
    (indices : list I)
    (term : I -> R) : R :=
  match indices with
  | nil => q1551745_zero ring
  | cons i rest =>
      q1551745_add ring
        (term i)
        (q1551745_sum_list ring rest term)
  end.

Definition q1551745_finite_sum {I R : Type}
    (ring : q1551745_ring R)
    (fin : q1551745_finite_type I)
    (term : I -> R) : R :=
  q1551745_sum_list ring (q1551745_enum fin) term.

Definition q1551745_identity_matrix {I R : Type}
    (ring : q1551745_ring R)
    (fin : q1551745_finite_type I) :
    q1551745_matrix I I R :=
  fun i j =>
    if q1551745_eq_dec fin i j
    then q1551745_one ring
    else q1551745_zero ring.

Definition q1551745_matrix_add {I J R : Type}
    (ring : q1551745_ring R)
    (A B : q1551745_matrix I J R) :
    q1551745_matrix I J R :=
  fun i j => q1551745_add ring (A i j) (B i j).

Definition q1551745_matrix_neg {I J R : Type}
    (ring : q1551745_ring R)
    (A : q1551745_matrix I J R) :
    q1551745_matrix I J R :=
  fun i j => q1551745_neg ring (A i j).

Definition q1551745_matrix_sub {I J R : Type}
    (ring : q1551745_ring R)
    (A B : q1551745_matrix I J R) :
    q1551745_matrix I J R :=
  q1551745_matrix_add ring A (q1551745_matrix_neg ring B).

Definition q1551745_matrix_mul {I J K R : Type}
    (ring : q1551745_ring R)
    (fin : q1551745_finite_type J)
    (A : q1551745_matrix I J R)
    (B : q1551745_matrix J K R) :
    q1551745_matrix I K R :=
  fun i k =>
    q1551745_finite_sum ring fin
      (fun j => q1551745_mul ring (A i j) (B j k)).

Record q1551745_invertible {I R : Type}
    (ring : q1551745_ring R)
    (fin : q1551745_finite_type I)
    (A : q1551745_matrix I I R) : Type := {
  q1551745_inverse : q1551745_matrix I I R;
  q1551745_inverse_mul_self :
    q1551745_matrix_equal
      (q1551745_matrix_mul ring fin q1551745_inverse A)
      (q1551745_identity_matrix ring fin);
  q1551745_mul_inverse_self :
    q1551745_matrix_equal
      (q1551745_matrix_mul ring fin A q1551745_inverse)
      (q1551745_identity_matrix ring fin)
}.

Arguments q1551745_inverse {I R ring fin A} _.

Definition q1551745_updated_matrix
    {N M R : Type}
    (ring : q1551745_ring R)
    (finM : q1551745_finite_type M)
    (A : q1551745_matrix N N R)
    (U : q1551745_matrix N M R)
    (C : q1551745_matrix M M R)
    (V : q1551745_matrix M N R) :
    q1551745_matrix N N R :=
  q1551745_matrix_add ring A
    (q1551745_matrix_mul ring finM
      (q1551745_matrix_mul ring finM U C)
      V).

Definition q1551745_auxiliary_matrix
    {N M R : Type}
    (ring : q1551745_ring R)
    (finN : q1551745_finite_type N)
    (finM : q1551745_finite_type M)
    (A_inverse : q1551745_matrix N N R)
    (U : q1551745_matrix N M R)
    (C : q1551745_matrix M M R)
    (V : q1551745_matrix M N R) :
    q1551745_matrix M M R :=
  q1551745_matrix_add ring C
    (q1551745_matrix_mul ring finM
      (q1551745_matrix_mul ring finN
        (q1551745_matrix_mul ring finN
          (q1551745_matrix_mul ring finM C V)
          A_inverse)
        U)
      C).

Definition q1551745_inverse_formula
    {N M R : Type}
    (ring : q1551745_ring R)
    (finN : q1551745_finite_type N)
    (finM : q1551745_finite_type M)
    (A_inverse : q1551745_matrix N N R)
    (auxiliary_inverse : q1551745_matrix M M R)
    (U : q1551745_matrix N M R)
    (C : q1551745_matrix M M R)
    (V : q1551745_matrix M N R) :
    q1551745_matrix N N R :=
  q1551745_matrix_sub ring A_inverse
    (q1551745_matrix_mul ring finN
      (q1551745_matrix_mul ring finM
        (q1551745_matrix_mul ring finM
          (q1551745_matrix_mul ring finM
            (q1551745_matrix_mul ring finM
              (q1551745_matrix_mul ring finN A_inverse U)
              C)
            auxiliary_inverse)
          C)
        V)
      A_inverse).

Theorem Matrix_invOf_add_mul_mul_prime :
  forall
    (R N M : Type)
    (ring : q1551745_ring R)
    (finN : q1551745_finite_type N)
    (finM : q1551745_finite_type M)
    (A : q1551745_matrix N N R)
    (U : q1551745_matrix N M R)
    (C : q1551745_matrix M M R)
    (V : q1551745_matrix M N R)
    (invertible_A : q1551745_invertible ring finN A)
    (invertible_auxiliary :
      q1551745_invertible ring finM
        (q1551745_auxiliary_matrix ring finN finM
          (q1551745_inverse invertible_A) U C V))
    (invertible_updated :
      q1551745_invertible ring finN
        (q1551745_updated_matrix ring finM A U C V)),
    q1551745_matrix_equal
      (q1551745_inverse invertible_updated)
      (q1551745_inverse_formula ring finN finM
        (q1551745_inverse invertible_A)
        (q1551745_inverse invertible_auxiliary)
        U C V).
Admitted.
