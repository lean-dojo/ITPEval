(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.let_clause_1545 (catalog title "gcd.let_clause_1545"): a nested
  natural-number statement in which zero divides two inputs to a gcd and
  explicit zero-product equalities imply that the first input is zero.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Theorem let_clause_1545 :
  forall m n : nat,
    Nat.gcd m n = 0 ->
    gcd_divides 0 n ->
    forall q1 : nat,
      n = 0 * q1 ->
      gcd_divides 0 m ->
      forall q2 : nat,
        m = 0 * q2 ->
        m = 0.
Admitted.
