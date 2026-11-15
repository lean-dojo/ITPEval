(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.prime_to_gcd_1 (catalog title "gcd.prime_to_gcd_1"): if a natural
  prime does not divide another natural number, then their greatest common
  divisor is one. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Definition gcd_prime (p : nat) : Prop :=
  1 < p /\
  forall divisor : nat,
    gcd_divides divisor p ->
    1 < divisor ->
    divisor = p.

Theorem prime_to_gcd_1 :
  forall n m : nat,
    gcd_prime n ->
    ~ gcd_divides n m ->
    Nat.gcd n m = 1.
Admitted.
