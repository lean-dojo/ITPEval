(* Statement-only formalization of Logipedia corpus artifact bigops.assoc:
   associativity of multiplication on natural numbers. This file contains
   no proof. *)

From Stdlib Require Import Arith.PeanoNat.

Theorem bigops_assoc :
  forall a b c : nat,
    Nat.mul a (Nat.mul b c) = Nat.mul (Nat.mul a b) c.
Admitted.
