(*
  Statement-only formalization of Logipedia corpus artifact primes.divides_n_n
  (catalog title "primes.divides_n_n"): every natural number divides itself.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem divides_n_n :
  forall n : nat,
    primes_divides n n.
Admitted.
