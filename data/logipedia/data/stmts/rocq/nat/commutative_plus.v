(*
  Statement-only formalization of Logipedia corpus artifact
  nat.commutative_plus (catalog title "nat.commutative_plus"): addition of
  natural numbers is commutative. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_commutative_plus :
  forall x y : nat,
    Nat.add x y = Nat.add y x.
Admitted.
