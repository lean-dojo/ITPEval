(*
  Statement-only formalization of Hundred Theorems artifact 048, "Dirichlet's Theorem".
  Every residue class coprime to a positive natural modulus contains arbitrarily large natural
  prime numbers. This file contains no proof.
*)

From Stdlib Require Import PeanoNat.

Definition is_prime (p : nat) : Prop :=
  2 <= p /\
  forall a b : nat,
    p = a * b ->
    a = 1 \/ b = 1.

Theorem dirichlets_theorem :
  forall d k : nat,
    1 <= d ->
    Nat.gcd k d = 1 ->
    forall n : nat,
      exists p : nat,
        n < p /\
        is_prime p /\
        Nat.modulo p d = Nat.modulo k d.
Admitted.
