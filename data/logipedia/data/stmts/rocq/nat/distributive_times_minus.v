(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_minus (catalog title
  "nat.distributive_times_minus"): natural-number multiplication distributes
  over truncated subtraction on the left. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_distributive_times_minus :
  forall a b c : nat,
    Nat.mul a (Nat.sub b c) =
    Nat.sub (Nat.mul a b) (Nat.mul a c).
Admitted.
