(*
  Statement-only formalization of Logipedia corpus artifact
  primes.not_divides_to_dividesb_false (catalog title
  "primes.not_divides_to_dividesb_false"): for a positive natural divisor,
  non-divisibility implies that the source Boolean remainder test is false.
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

Theorem logipedia_primes_not_divides_to_dividesb_false :
  forall n m : nat,
    O < n ->
    ~ primes_divides n m ->
    primes_dividesb n m = false.
Admitted.
