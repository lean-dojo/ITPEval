(*
  Statement-only formalization of Logipedia corpus artifact
  primes.mod_O_to_divides (catalog title "primes.mod_O_to_divides"): if a
  positive natural number gives zero remainder when dividing another natural
  number, then it divides that number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_source_mod (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => Nat.modulo m (S n')
  end.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem primes_mod_O_to_divides :
  forall n m : nat,
    O < n ->
    primes_source_mod m n = O ->
    primes_divides n m.
Admitted.
