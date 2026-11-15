(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_times_to_divides (catalog title
  "gcd.divides_times_to_divides"): a natural prime dividing a product divides
  at least one of its factors. This file contains no proof.
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

Theorem divides_times_to_divides :
  forall p n m : nat,
    gcd_prime p ->
    gcd_divides p (n * m) ->
    gcd_divides p n \/ gcd_divides p m.
Admitted.
