(*
  Statement-only formalization of Logipedia corpus artifact
  primes.let_clause_15311 (catalog title "primes.let_clause_15311"): for
  natural numbers n, m, d, and p, if m is positive, n divides m, and m equals
  n times the successor of p, then m equals n plus n times p. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_let_clause_15311 :
  forall n m : nat,
    O < m ->
    primes_divides n m ->
    forall d p : nat,
      m = n * S p ->
      m = n + n * p.
Admitted.
