(*
  Statement-only formalization of Logipedia corpus artifact
  primes.let_clause_1531 (catalog title "primes.let_clause_1531"): for natural
  numbers n, m, and d, if m is positive, n divides m, and m equals n times
  zero, then m equals zero. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_let_clause_1531 :
  forall n m : nat,
    O < m ->
    primes_divides n m ->
    forall d : nat,
      m = n * O ->
      m = O.
Admitted.
