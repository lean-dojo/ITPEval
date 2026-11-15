(*
  Statement-only formalization of Logipedia corpus artifact
  nat.minus_minus_comm (catalog title "nat.minus_minus_comm"): iterated
  truncated subtraction on natural numbers is unchanged when the two
  subtrahends are exchanged. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_minus_minus_comm :
  forall a b c : nat,
    Nat.sub (Nat.sub a b) c = Nat.sub (Nat.sub a c) b.
Admitted.
