(*
  Statement-only formalization of Logipedia corpus artifact
  gcd.divides_gcd_nm (catalog title "gcd.divides_gcd_nm"): the greatest
  common divisor of two natural numbers divides both the second number and
  the first number. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Definition gcd_divides (divisor value : nat) : Prop :=
  exists quotient : nat, value = divisor * quotient.

Theorem divides_gcd_nm :
  forall n m : nat,
    gcd_divides (Nat.gcd n m) m /\
    gcd_divides (Nat.gcd n m) n.
Admitted.
