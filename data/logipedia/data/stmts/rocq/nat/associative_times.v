(*
  Statement-only formalization of Logipedia corpus artifact
  nat.associative_times (catalog title "nat.associative_times"):
  multiplication of natural numbers is associative. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_associative_times :
  forall x y z : nat,
    Nat.mul (Nat.mul x y) z = Nat.mul x (Nat.mul y z).
Admitted.
