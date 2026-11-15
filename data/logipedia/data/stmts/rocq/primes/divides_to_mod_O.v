(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_mod_O (catalog title "primes.divides_to_mod_O"):
  a positive natural number that divides another has zero remainder modulo
  that divisor. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_source_mod (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => Nat.modulo m (S n')
  end.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem primes_divides_to_mod_O :
  forall n m : nat,
    O < n ->
    primes_divides n m ->
    primes_source_mod m n = O.
Admitted.
