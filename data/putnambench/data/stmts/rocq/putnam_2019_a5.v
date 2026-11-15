(* Statement-only formalization of PutnamBench corpus artifact putnam_2019_a5:
   the greatest power of X - 1 dividing a specified polynomial over the
   finite field F_p is (p - 1) / 2. This file contains no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Definition putnam_2019_a5_divides_nat (a b : nat) : Prop :=
  exists c : nat, b = a * c.

Definition putnam_2019_a5_prime (p : nat) : Prop :=
  (2 <= p)%nat /\
  forall d : nat,
    putnam_2019_a5_divides_nat d p ->
    d = 1%nat \/ d = p.

Definition putnam_2019_a5_odd (p : nat) : Prop :=
  exists m : nat, p = (2 * m + 1)%nat.

Fixpoint putnam_2019_a5_sum_to
    (n : nat) (f : nat -> nat) : nat :=
  match n with
  | O => f O
  | S k => (putnam_2019_a5_sum_to k f + f (S k))%nat
  end.

Definition putnam_2019_a5_polynomial
    (p : nat) (coefficients : nat -> nat) : Prop :=
  (forall k : nat, (coefficients k < p)%nat) /\
  exists bound : nat,
    forall k : nat,
      (bound < k)%nat ->
      coefficients k = 0%nat.

Definition putnam_2019_a5_poly_mul
    (p : nat)
    (f g : nat -> nat)
    (degree : nat) : nat :=
  Nat.modulo
    (putnam_2019_a5_sum_to degree
      (fun k : nat => (f k * g (degree - k))%nat))
    p.

Definition putnam_2019_a5_one_coeff
    (p degree : nat) : nat :=
  if Nat.eqb degree 0%nat then Nat.modulo 1%nat p else 0%nat.

Definition putnam_2019_a5_X_minus_one_coeff
    (p degree : nat) : nat :=
  if Nat.eqb degree 0%nat then (p - 1)%nat
  else if Nat.eqb degree 1%nat then 1%nat
  else 0%nat.

Fixpoint putnam_2019_a5_X_minus_one_pow
    (p exponent : nat) : nat -> nat :=
  match exponent with
  | O => putnam_2019_a5_one_coeff p
  | S previous =>
      putnam_2019_a5_poly_mul p
        (putnam_2019_a5_X_minus_one_coeff p)
        (putnam_2019_a5_X_minus_one_pow p previous)
  end.

Definition putnam_2019_a5_q_coeff
    (p k : nat) : nat :=
  if Nat.eqb k 0%nat then 0%nat
  else if Nat.leb p k then 0%nat
  else Nat.modulo (Nat.pow k ((p - 1) / 2)) p.

Definition putnam_2019_a5_poly_divides
    (p : nat)
    (factor product : nat -> nat) : Prop :=
  exists quotient : nat -> nat,
    putnam_2019_a5_polynomial p quotient /\
    forall degree : nat,
      product degree =
      putnam_2019_a5_poly_mul p factor quotient degree.

Definition putnam_2019_a5_qualifies
    (p exponent : nat) : Prop :=
  putnam_2019_a5_poly_divides p
    (putnam_2019_a5_X_minus_one_pow p exponent)
    (putnam_2019_a5_q_coeff p).

Definition putnam_2019_a5_is_greatest
    (P : nat -> Prop) (greatest : nat) : Prop :=
  P greatest /\
  forall n : nat, P n -> (n <= greatest)%nat.

Theorem putnam_2019_a5
    (p : nat)
    (podd : putnam_2019_a5_odd p)
    (pprime : putnam_2019_a5_prime p) :
  putnam_2019_a5_is_greatest
    (putnam_2019_a5_qualifies p)
    ((p - 1) / 2).
Admitted.
