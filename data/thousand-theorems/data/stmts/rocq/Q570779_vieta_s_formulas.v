(*
  Statement-only formalization of Thousand Theorems corpus artifact Q570779
  (thousand-theorems__rocq__Q570779), "Vieta's formulas": over an arbitrary
  commutative semiring, the product of the linear polynomials X + C(r) for a
  multiset of coefficients is the sum whose coefficients are its elementary
  symmetric functions. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat List Sorting.Permutation.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q570779_comm_semiring (R : Type) : Type := {
  q570779_zero : R;
  q570779_one : R;
  q570779_add : R -> R -> R;
  q570779_mul : R -> R -> R;
  q570779_add_assoc :
    forall x y z : R,
      q570779_add x (q570779_add y z) =
      q570779_add (q570779_add x y) z;
  q570779_add_comm :
    forall x y : R,
      q570779_add x y = q570779_add y x;
  q570779_add_zero_left :
    forall x : R, q570779_add q570779_zero x = x;
  q570779_add_zero_right :
    forall x : R, q570779_add x q570779_zero = x;
  q570779_mul_assoc :
    forall x y z : R,
      q570779_mul x (q570779_mul y z) =
      q570779_mul (q570779_mul x y) z;
  q570779_mul_comm :
    forall x y : R,
      q570779_mul x y = q570779_mul y x;
  q570779_mul_one_left :
    forall x : R, q570779_mul q570779_one x = x;
  q570779_mul_one_right :
    forall x : R, q570779_mul x q570779_one = x;
  q570779_mul_zero_left :
    forall x : R, q570779_mul q570779_zero x = q570779_zero;
  q570779_mul_zero_right :
    forall x : R, q570779_mul x q570779_zero = q570779_zero;
  q570779_mul_add_left :
    forall x y z : R,
      q570779_mul x (q570779_add y z) =
      q570779_add (q570779_mul x y) (q570779_mul x z);
  q570779_mul_add_right :
    forall x y z : R,
      q570779_mul (q570779_add x y) z =
      q570779_add (q570779_mul x z) (q570779_mul y z)
}.

Arguments q570779_zero {R} _.
Arguments q570779_one {R} _.
Arguments q570779_add {R} _ _ _.
Arguments q570779_mul {R} _ _ _.

Definition q570779_multiset (R : Type) : Type := list R.

Definition q570779_multiset_equiv {R : Type}
    (s t : q570779_multiset R) : Prop :=
  Permutation s t.

Fixpoint q570779_sum_range
    {R : Type} (SR : q570779_comm_semiring R)
    (f : nat -> R) (n : nat) : R :=
  match n with
  | O => q570779_zero SR
  | S k =>
      q570779_add SR
        (q570779_sum_range SR f k) (f k)
  end.

Definition q570779_polynomial (R : Type) : Type :=
  nat -> R.

Definition q570779_polynomial_equal {R : Type}
    (p q : q570779_polynomial R) : Prop :=
  forall k : nat, p k = q k.

Definition q570779_polynomial_zero
    {R : Type} (SR : q570779_comm_semiring R)
    : q570779_polynomial R :=
  fun _ => q570779_zero SR.

Definition q570779_polynomial_one
    {R : Type} (SR : q570779_comm_semiring R)
    : q570779_polynomial R :=
  fun k =>
    match k with
    | O => q570779_one SR
    | S _ => q570779_zero SR
    end.

Definition q570779_polynomial_X
    {R : Type} (SR : q570779_comm_semiring R)
    : q570779_polynomial R :=
  fun k =>
    match k with
    | S O => q570779_one SR
    | _ => q570779_zero SR
    end.

Definition q570779_polynomial_C
    {R : Type} (SR : q570779_comm_semiring R)
    (r : R) : q570779_polynomial R :=
  fun k =>
    match k with
    | O => r
    | S _ => q570779_zero SR
    end.

Definition q570779_polynomial_add
    {R : Type} (SR : q570779_comm_semiring R)
    (p q : q570779_polynomial R) : q570779_polynomial R :=
  fun k => q570779_add SR (p k) (q k).

Definition q570779_polynomial_mul
    {R : Type} (SR : q570779_comm_semiring R)
    (p q : q570779_polynomial R) : q570779_polynomial R :=
  fun n =>
    q570779_sum_range SR
      (fun i =>
        q570779_mul SR (p i) (q (Nat.sub n i)))
      (S n).

Fixpoint q570779_polynomial_pow
    {R : Type} (SR : q570779_comm_semiring R)
    (p : q570779_polynomial R) (n : nat)
    : q570779_polynomial R :=
  match n with
  | O => q570779_polynomial_one SR
  | S k =>
      q570779_polynomial_mul SR p
        (q570779_polynomial_pow SR p k)
  end.

Fixpoint q570779_polynomial_product
    {R : Type} (SR : q570779_comm_semiring R)
    (polynomials : list (q570779_polynomial R))
    : q570779_polynomial R :=
  match polynomials with
  | nil => q570779_polynomial_one SR
  | p :: rest =>
      q570779_polynomial_mul SR p
        (q570779_polynomial_product SR rest)
  end.

Fixpoint q570779_polynomial_sum_range
    {R : Type} (SR : q570779_comm_semiring R)
    (f : nat -> q570779_polynomial R) (n : nat)
    : q570779_polynomial R :=
  match n with
  | O => q570779_polynomial_zero SR
  | S k =>
      q570779_polynomial_add SR
        (q570779_polynomial_sum_range SR f k) (f k)
  end.

Fixpoint q570779_esymm
    {R : Type} (SR : q570779_comm_semiring R)
    (s : q570779_multiset R) (k : nat) {struct s} : R :=
  match s, k with
  | _, O => q570779_one SR
  | nil, S _ => q570779_zero SR
  | r :: rest, S j =>
      q570779_add SR
        (q570779_esymm SR rest (S j))
        (q570779_mul SR r (q570779_esymm SR rest j))
  end.

Theorem Multiset_prod_X_add_C_eq_sum_esymm :
  forall
      (R : Type)
      (SR : q570779_comm_semiring R)
      (s : q570779_multiset R),
    q570779_polynomial_equal
      (q570779_polynomial_product SR
        (map
          (fun r : R =>
            q570779_polynomial_add SR
              (q570779_polynomial_X SR)
              (q570779_polynomial_C SR r))
          s))
      (q570779_polynomial_sum_range SR
        (fun j : nat =>
          q570779_polynomial_mul SR
            (q570779_polynomial_C SR (q570779_esymm SR s j))
            (q570779_polynomial_pow SR
              (q570779_polynomial_X SR)
              (Nat.sub (length s) j)))
        (S (length s))).
Admitted.
