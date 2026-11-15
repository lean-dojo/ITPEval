(*
  Statement-only formalization of Logipedia corpus artifact primes.divides_to_le
  (catalog title "primes.divides_to_le"): if a natural number divides a
  positive natural number, then the divisor is at most that number.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_divides_to_le :
  forall n m : nat,
    O < m ->
    primes_divides n m ->
    n <= m.
Admitted.
