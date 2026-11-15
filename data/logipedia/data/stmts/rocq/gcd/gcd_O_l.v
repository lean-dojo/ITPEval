(*
  Statement-only formalization of Logipedia corpus artifact gcd.gcd_O_l
  (catalog title "gcd.gcd_O_l"): zero is a left identity for the greatest
  common divisor on natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem gcd_O_l :
  forall m : nat,
    Nat.gcd 0 m = m.
Admitted.
