(*
  Statement-only formalization of Logipedia corpus artifact gcd.divides_gcd_r
  (catalog title "gcd.divides_gcd_r"): the greatest common divisor of two
  natural numbers divides the second number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Theorem divides_gcd_r :
  forall n m : nat,
    gcd_divides (Nat.gcd n m) m.
Admitted.
