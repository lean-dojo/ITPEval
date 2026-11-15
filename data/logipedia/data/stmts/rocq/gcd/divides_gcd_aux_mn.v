(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_aux_mn (catalog title "gcd.divides_gcd_aux_mn"): for
  natural numbers p, m, and positive n with n at most m and p, the
  fuel-recursive auxiliary gcd value divides both m and n. This file contains
  no proof.
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

Theorem divides_gcd_aux_mn :
  forall p m n : nat,
    O < n ->
    n <= m ->
    n <= p ->
    gcd_divides (gcd_aux p m n) m /\
    gcd_divides (gcd_aux p m n) n.
Admitted.
