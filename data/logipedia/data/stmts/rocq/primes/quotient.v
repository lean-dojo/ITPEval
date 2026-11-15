(*
  Statement-only formalization of Logipedia corpus artifact primes.quotient
  (catalog title "primes.quotient"): if a natural number m equals n times a
  natural quotient q, then n divides m. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_quotient :
  forall n m q : nat,
    m = n * q ->
    primes_divides n m.
Admitted.
