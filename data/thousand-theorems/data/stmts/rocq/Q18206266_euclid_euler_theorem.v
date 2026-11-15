(*
  Statement-only formalization of Thousand Theorems corpus artifact Q18206266
  (thousand-theorems__rocq__Q18206266), "Euclid–Euler theorem": every even
  perfect natural number is a power of two times a prime Mersenne number.
  This file contains no proof.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat.

Definition q18206266_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Definition q18206266_mersenne (exponent : nat) : nat :=
  Nat.pow 2 exponent - 1.

Definition q18206266_sum_proper_divisors (n : nat) : nat :=
  fold_right Nat.add 0
    (filter
      (fun d : nat => Nat.eqb (Nat.modulo n d) 0)
      (seq 1 (n - 1))).

Definition q18206266_perfect (n : nat) : Prop :=
  q18206266_sum_proper_divisors n = n /\ (0 < n)%nat.

Theorem eq_two_pow_mul_prime_mersenne_of_even_perfect :
  forall n : nat,
    Nat.Even n ->
    q18206266_perfect n ->
    exists k : nat,
      q18206266_prime (q18206266_mersenne (k + 1)) /\
      n = Nat.pow 2 k * q18206266_mersenne (k + 1).
Admitted.
