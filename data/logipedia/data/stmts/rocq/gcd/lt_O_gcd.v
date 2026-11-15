(*
  Statement-only formalization of Logipedia corpus artifact gcd.lt_O_gcd
  (catalog title "gcd.lt_O_gcd"): a greatest common divisor of natural
  numbers is positive when the second number is positive. This file contains
  no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem lt_O_gcd :
  forall m n : nat,
    0 < n -> 0 < Nat.gcd m n.
Admitted.
