(*
  Statement-only formalization of Logipedia corpus artifact
  nat.commutative_times (catalog title "nat.commutative_times"):
  multiplication of natural numbers is commutative. This file contains no
  proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_commutative_times :
  forall x y : nat,
    Nat.mul x y = Nat.mul y x.
Admitted.
