(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_le_minus_l (catalog title "nat.monotonic_le_minus_l"):
  truncated subtraction on natural numbers is monotone in its left operand.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_le_minus_l :
  forall p q n : nat,
    Nat.le q p ->
    Nat.le (Nat.sub q n) (Nat.sub p n).
Admitted.
