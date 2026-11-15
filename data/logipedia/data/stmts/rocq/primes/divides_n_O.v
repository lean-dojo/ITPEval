(*
  Statement-only formalization of Logipedia corpus artifact primes.divides_n_O
  (catalog title "primes.divides_n_O"): every natural number divides zero.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Theorem logipedia_primes_divides_n_O :
  forall n : nat,
    primes_divides n 0.
Admitted.
