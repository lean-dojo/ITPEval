(*
  Statement-only formalization of Logipedia corpus artifact
  primes.prime_to_lt_SO (catalog title "primes.prime_to_lt_SO"): every
  natural number satisfying the source prime predicate is greater than one.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Definition primes_prime (n : nat) : Prop :=
  1 < n /\
  forall m : nat,
    primes_divides m n ->
    1 < m ->
    m = n.

Theorem prime_to_lt_SO :
  forall p : nat,
    primes_prime p ->
    1 < p.
Admitted.
