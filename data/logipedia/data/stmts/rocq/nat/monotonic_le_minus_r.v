(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_minus_r (catalog title "nat.monotonic_le_minus_r"):
  truncated subtraction on natural numbers reverses order in its right
  operand. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_le_minus_r :
  forall p q n : nat,
    Nat.le q p ->
    Nat.le (Nat.sub n p) (Nat.sub n q).
Admitted.
