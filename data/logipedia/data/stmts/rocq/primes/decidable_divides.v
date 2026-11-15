(*
  Statement-only formalization of Logipedia corpus artifact
  primes.decidable_divides (catalog title "primes.decidable_divides"):
  divisibility is decidable for every pair of natural numbers. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_decidable_divides :
  forall n m : nat,
    primes_divides n m \/ ~ primes_divides n m.
Admitted.
