(*
  Statement-only formalization of Logipedia corpus artifact
  nat.associative_plus (catalog title "nat.associative_plus"): addition of
  natural numbers is associative. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_associative_plus :
  forall x y z : nat,
    Nat.add (Nat.add x y) z = Nat.add x (Nat.add y z).
Admitted.
