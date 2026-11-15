(*
  Statement-only formalization of Thousand Theorems corpus artifact Q914517
  (thousand-theorems__rocq__Q914517), "Fermat's theorem on sums of two
  squares": every prime natural number not congruent to 3 modulo 4 is a sum
  of two squares of natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition q914517_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Theorem Nat_Prime_sq_add_sq :
  forall p : nat,
    q914517_prime p ->
    Nat.modulo p 4 <> 3 ->
    exists a b : nat,
      Nat.pow a 2 + Nat.pow b 2 = p.
Admitted.
