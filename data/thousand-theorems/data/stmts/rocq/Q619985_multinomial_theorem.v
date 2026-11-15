(*
  Statement-only formalization of Thousand Theorems corpus artifact Q619985
  (thousand-theorems__rocq__Q619985), "Multinomial theorem": for pairwise
  commuting values indexed by a finite set in a semiring, the power of their
  sum is the multinomial sum over exponent assignments of the same total
  degree. This file contains no proof.
*)

From Stdlib Require Import List Arith.PeanoNat.

Import ListNotations.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q619985_semiring (R : Type) : Type := {
  q619985_zero : R;
  q619985_one : R;
  q619985_add : R -> R -> R;
  q619985_mul : R -> R -> R;
  q619985_add_assoc :
    forall x y z : R,
      q619985_add x (q619985_add y z) =
      q619985_add (q619985_add x y) z;
  q619985_add_comm :
    forall x y : R,
      q619985_add x y = q619985_add y x;
  q619985_zero_add :
    forall x : R, q619985_add q619985_zero x = x;
  q619985_add_zero :
    forall x : R, q619985_add x q619985_zero = x;
  q619985_mul_assoc :
    forall x y z : R,
      q619985_mul x (q619985_mul y z) =
      q619985_mul (q619985_mul x y) z;
  q619985_one_mul :
    forall x : R, q619985_mul q619985_one x = x;
  q619985_mul_one :
    forall x : R, q619985_mul x q619985_one = x;
  q619985_mul_add :
    forall x y z : R,
      q619985_mul x (q619985_add y z) =
      q619985_add
        (q619985_mul x y) (q619985_mul x z);
  q619985_add_mul :
    forall x y z : R,
      q619985_mul (q619985_add x y) z =
      q619985_add
        (q619985_mul x z) (q619985_mul y z);
  q619985_zero_mul :
    forall x : R, q619985_mul q619985_zero x = q619985_zero;
  q619985_mul_zero :
    forall x : R, q619985_mul x q619985_zero = q619985_zero
}.

Arguments q619985_zero {R} _.
Arguments q619985_one {R} _.
Arguments q619985_add {R} _ _ _.
Arguments q619985_mul {R} _ _ _.

Fixpoint q619985_pow
    {R : Type}
    (SR : q619985_semiring R)
    (x : R) (n : nat) : R :=
  match n with
  | O => q619985_one SR
  | S k => q619985_mul SR x (q619985_pow SR x k)
  end.

Fixpoint q619985_nat_cast
    {R : Type}
    (SR : q619985_semiring R)
    (n : nat) : R :=
  match n with
  | O => q619985_zero SR
  | S k =>
      q619985_add SR (q619985_nat_cast SR k) (q619985_one SR)
  end.

Fixpoint q619985_factorial (n : nat) : nat :=
  match n with
  | O => 1
  | S k => S k * q619985_factorial k
  end.

Fixpoint q619985_sum_exponents
    {A : Type}
    (indices : list A)
    (k : A -> nat) : nat :=
  match indices with
  | [] => O
  | i :: rest => k i + q619985_sum_exponents rest k
  end.

Fixpoint q619985_factorial_product
    {A : Type}
    (indices : list A)
    (k : A -> nat) : nat :=
  match indices with
  | [] => 1
  | i :: rest =>
      q619985_factorial (k i) *
      q619985_factorial_product rest k
  end.

Definition q619985_multinomial
    {A : Type}
    (indices : list A)
    (k : A -> nat) : nat :=
  Nat.div
    (q619985_factorial (q619985_sum_exponents indices k))
    (q619985_factorial_product indices k).

Fixpoint q619985_compositions
    (number_of_indices total_degree : nat) : list (list nat) :=
  match number_of_indices with
  | O =>
      match total_degree with
      | O => [[]]
      | S _ => []
      end
  | S smaller_number =>
      flat_map
        (fun exponent =>
          map
            (fun remaining => exponent :: remaining)
            (q619985_compositions
              smaller_number (Nat.sub total_degree exponent)))
        (seq O (S total_degree))
  end.

Fixpoint q619985_exponent_function
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (indices : list A)
    (exponents : list nat)
    (x : A) : nat :=
  match indices, exponents with
  | i :: rest_indices, exponent :: rest_exponents =>
      if eq_dec x i
      then exponent
      else
        q619985_exponent_function
          eq_dec rest_indices rest_exponents x
  | _, _ => O
  end.

Definition q619985_pi_antidiag
    {A : Type}
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (indices : list A)
    (total_degree : nat) : list (A -> nat) :=
  map
    (fun exponents =>
      q619985_exponent_function eq_dec indices exponents)
    (q619985_compositions (length indices) total_degree).

Fixpoint q619985_sum
    {A R : Type}
    (SR : q619985_semiring R)
    (f : A -> R)
    (indices : list A) : R :=
  match indices with
  | [] => q619985_zero SR
  | i :: rest =>
      q619985_add SR (f i) (q619985_sum SR f rest)
  end.

Fixpoint q619985_product_of_powers
    {A R : Type}
    (SR : q619985_semiring R)
    (f : A -> R)
    (indices : list A)
    (k : A -> nat) : R :=
  match indices with
  | [] => q619985_one SR
  | i :: rest_indices =>
      q619985_mul SR
        (q619985_pow SR (f i) (k i))
        (q619985_product_of_powers
          SR f rest_indices k)
  end.

Fixpoint q619985_multinomial_sum
    {A R : Type}
    (SR : q619985_semiring R)
    (f : A -> R)
    (indices : list A)
    (exponent_assignments : list (A -> nat)) : R :=
  match exponent_assignments with
  | [] => q619985_zero SR
  | k :: rest =>
      q619985_add SR
        (q619985_mul SR
          (q619985_nat_cast SR
            (q619985_multinomial indices k))
          (q619985_product_of_powers
            SR f indices k))
        (q619985_multinomial_sum SR f indices rest)
  end.

Definition q619985_pairwise_commute
    {A R : Type}
    (SR : q619985_semiring R)
    (f : A -> R)
    (indices : list A) : Prop :=
  forall x y : A,
    In x indices ->
    In y indices ->
    x <> y ->
    q619985_mul SR (f x) (f y) =
    q619985_mul SR (f y) (f x).

Theorem sum_pow_eq_sum_piAntidiag_of_commute :
  forall
    (A R : Type)
    (eq_dec : forall x y : A, {x = y} + {x <> y})
    (SR : q619985_semiring R)
    (indices : list A)
    (f : A -> R),
    NoDup indices ->
    q619985_pairwise_commute SR f indices ->
    forall n : nat,
    q619985_pow SR (q619985_sum SR f indices) n =
    q619985_multinomial_sum
      SR f indices (q619985_pi_antidiag eq_dec indices n).
Admitted.
