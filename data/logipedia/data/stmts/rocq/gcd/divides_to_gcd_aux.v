(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_to_gcd_aux (catalog title "gcd.divides_to_gcd_aux"): for
  natural numbers p, m, and n, if p and n are positive and n divides m, then
  the fuel-recursive auxiliary gcd value at p, m, and n equals n. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Fixpoint gcd_aux (p m n : nat) : nat :=
  match p with
  | O => m
  | S q =>
      if Nat.eqb (Nat.modulo m n) O
      then n
      else gcd_aux q n (Nat.modulo m n)
  end.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Theorem divides_to_gcd_aux :
  forall p m n : nat,
    O < p ->
    O < n ->
    gcd_divides n m ->
    gcd_aux p m n = n.
Admitted.
