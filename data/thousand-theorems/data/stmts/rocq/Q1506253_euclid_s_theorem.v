(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1506253
  (thousand-theorems__rocq__Q1506253), "Euclid's theorem": for every natural
  number n, there exists a prime natural number p with n <= p. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition q1506253_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Theorem exists_infinite_primes :
  forall n : nat,
    exists p : nat,
      (n <= p)%nat /\ q1506253_prime p.
Admitted.
