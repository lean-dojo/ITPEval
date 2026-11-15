(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_plus_r (catalog title
  "nat.distributive_times_plus_r"): right multiplication distributes over
  addition on natural numbers. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_distributive_times_plus_r :
  forall a b c : nat,
    Nat.mul (Nat.add b c) a =
    Nat.add (Nat.mul b a) (Nat.mul c a).
Admitted.
