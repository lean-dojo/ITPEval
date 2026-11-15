(*
  Statement-only formalization of Logipedia corpus artifact
  primes.divides_to_dividesb_true (catalog title
  "primes.divides_to_dividesb_true"): for a positive natural divisor,
  divisibility implies that the source Boolean remainder test is true.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint div_mod_source_mod_aux (p n m : nat) {struct p} : nat :=
  match p with
  | O => n
  | S q =>
      if Nat.leb n m
      then n
      else div_mod_source_mod_aux q (n - S m) m
  end.

Definition div_mod_source_mod (n m : nat) : nat :=
  match m with
  | O => n
  | S p => div_mod_source_mod_aux n n p
  end.

Definition primes_divides (n m : nat) : Prop :=
  exists q : nat, m = n * q.

Definition primes_dividesb (n m : nat) : bool :=
  Nat.eqb (div_mod_source_mod m n) O.

Theorem logipedia_primes_divides_to_dividesb_true :
  forall n m : nat,
    O < n ->
    primes_divides n m ->
    primes_dividesb n m = true.
Admitted.
