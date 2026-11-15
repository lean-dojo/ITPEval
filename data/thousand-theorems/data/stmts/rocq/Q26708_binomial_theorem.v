(*
  Statement-only formalization of Thousand Theorems corpus artifact Q26708
  (thousand-theorems__rocq__Q26708), "Binomial theorem": in every
  commutative semiring, a natural power of a sum equals the finite binomial
  expansion. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Set Universe Polymorphism.
Set Implicit Arguments.

Record q26708_comm_semiring (R : Type) : Type := {
  q26708_zero : R;
  q26708_one : R;
  q26708_add : R -> R -> R;
  q26708_mul : R -> R -> R;
  q26708_add_assoc :
    forall x y z : R,
      q26708_add x (q26708_add y z) =
      q26708_add (q26708_add x y) z;
  q26708_add_comm :
    forall x y : R,
      q26708_add x y = q26708_add y x;
  q26708_add_zero_left :
    forall x : R, q26708_add q26708_zero x = x;
  q26708_add_zero_right :
    forall x : R, q26708_add x q26708_zero = x;
  q26708_mul_assoc :
    forall x y z : R,
      q26708_mul x (q26708_mul y z) =
      q26708_mul (q26708_mul x y) z;
  q26708_mul_comm :
    forall x y : R,
      q26708_mul x y = q26708_mul y x;
  q26708_mul_one_left :
    forall x : R, q26708_mul q26708_one x = x;
  q26708_mul_one_right :
    forall x : R, q26708_mul x q26708_one = x;
  q26708_mul_zero_left :
    forall x : R, q26708_mul q26708_zero x = q26708_zero;
  q26708_mul_zero_right :
    forall x : R, q26708_mul x q26708_zero = q26708_zero;
  q26708_mul_add_left :
    forall x y z : R,
      q26708_mul x (q26708_add y z) =
      q26708_add (q26708_mul x y) (q26708_mul x z);
  q26708_mul_add_right :
    forall x y z : R,
      q26708_mul (q26708_add x y) z =
      q26708_add (q26708_mul x z) (q26708_mul y z)
}.

Arguments q26708_zero {R} _.
Arguments q26708_one {R} _.
Arguments q26708_add {R} _ _ _.
Arguments q26708_mul {R} _ _ _.

Fixpoint q26708_pow
    {R : Type} (SR : q26708_comm_semiring R)
    (x : R) (n : nat) : R :=
  match n with
  | O => q26708_one SR
  | S k => q26708_mul SR x (q26708_pow SR x k)
  end.

Fixpoint q26708_nat_cast
    {R : Type} (SR : q26708_comm_semiring R)
    (n : nat) : R :=
  match n with
  | O => q26708_zero SR
  | S k => q26708_add SR (q26708_nat_cast SR k) (q26708_one SR)
  end.

Fixpoint q26708_choose (n k : nat) : nat :=
  match n, k with
  | _, O => 1
  | O, S _ => 0
  | S n', S k' =>
      q26708_choose n' k' + q26708_choose n' (S k')
  end.

Fixpoint q26708_sum_upto
    {R : Type} (SR : q26708_comm_semiring R)
    (f : nat -> R) (n : nat) : R :=
  match n with
  | O => f O
  | S k => q26708_add SR (q26708_sum_upto SR f k) (f (S k))
  end.

Theorem add_pow :
  forall
      (R : Type)
      (SR : q26708_comm_semiring R)
      (x y : R)
      (n : nat),
    q26708_pow SR (q26708_add SR x y) n =
    q26708_sum_upto SR
      (fun m : nat =>
        q26708_mul SR
          (q26708_mul SR
            (q26708_pow SR x m)
            (q26708_pow SR y (Nat.sub n m)))
          (q26708_nat_cast SR (q26708_choose n m)))
      n.
Admitted.
