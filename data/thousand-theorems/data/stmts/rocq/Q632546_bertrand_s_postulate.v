(*
  Statement-only formalization of Thousand Theorems corpus artifact Q632546
  (thousand-theorems__rocq__Q632546), "Bertrand's postulate": every nonzero
  natural number has a prime strictly greater than it and at most twice as
  large. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition q632546_prime (p : nat) : Prop :=
  (1 < p)%nat /\
  forall d : nat, Nat.divide d p -> d = 1 \/ d = p.

Theorem bertrand :
  forall n : nat,
    n <> 0 ->
    exists p : nat,
      q632546_prime p /\
      (n < p)%nat /\
      (p <= 2 * n)%nat.
Admitted.
