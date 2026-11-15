(*
  Statement-only formalization of Logipedia corpus artifact
  primes.prime_to_lt_O (catalog title "primes.prime_to_lt_O"): every prime
  natural number is strictly greater than zero. This file contains no proof.
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

Theorem logipedia_primes_prime_to_lt_O :
  forall p : nat,
    primes_prime p ->
    O < p.
Admitted.
