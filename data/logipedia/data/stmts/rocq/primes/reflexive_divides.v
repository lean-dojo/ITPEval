(*
  Statement-only formalization of Logipedia corpus artifact
  primes.reflexive_divides (catalog title "primes.reflexive_divides"): the
  natural-number divisibility relation is reflexive, so every natural number
  divides itself. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_reflexive_divides :
  forall n : nat,
    primes_divides n n.
Admitted.
