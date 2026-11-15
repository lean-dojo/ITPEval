(*
  Statement-only formalization of Logipedia corpus artifact
  primes.eq_mod_to_divides (catalog title "primes.eq_mod_to_divides"):
  equal remainders modulo a positive natural number imply that the modulus
  divides the truncated natural-number difference. This file contains no proof.
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
  exists k : nat, m = n * k.

Theorem logipedia_primes_eq_mod_to_divides :
  forall n m q : nat,
    O < q ->
    div_mod_source_mod n q = div_mod_source_mod m q ->
    primes_divides q (n - m).
Admitted.
