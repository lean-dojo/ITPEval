(*
  Statement-only formalization of Logipedia corpus artifact
  nat.distributive_times_plus (catalog title "nat.distributive_times_plus"):
  natural-number multiplication distributes over addition on the left. This
  file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_distributive_times_plus :
  forall x y z : nat,
    Nat.mul x (Nat.add y z) =
    Nat.add (Nat.mul x y) (Nat.mul x z).
Admitted.
