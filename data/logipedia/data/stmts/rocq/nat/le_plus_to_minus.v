(*
  Statement-only formalization of Logipedia corpus artifact
  nat.le_plus_to_minus (catalog title "nat.le_plus_to_minus"): for natural
  numbers n, m, and p, if n is at most p plus m, then the truncated
  difference n minus m is at most p. This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_le_plus_to_minus :
  forall n m p : nat,
    n <= Nat.add p m ->
    Nat.sub n m <= p.
Admitted.
