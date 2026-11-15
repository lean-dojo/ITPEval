(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.not_divides_to_gcd_aux (catalog title
  "gcd.not_divides_to_gcd_aux"): for natural numbers p, m, and positive n,
  if n does not divide m, then the successor-fuel auxiliary gcd call equals
  the recursive call on n and the remainder of m modulo n. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition gcd_source_modulo (m n : nat) : nat :=
  match n with
  | O => m
  | S n' => Nat.modulo m (S n')
  end.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Fixpoint gcd_aux (p m n : nat) : nat :=
  match p with
  | O => m
  | S q =>
      if Nat.eqb (gcd_source_modulo m n) O
      then n
      else gcd_aux q n (gcd_source_modulo m n)
  end.

Theorem not_divides_to_gcd_aux :
  forall p m n : nat,
    O < n ->
    ~ gcd_divides n m ->
    gcd_aux (S p) m n = gcd_aux p n (gcd_source_modulo m n).
Admitted.
