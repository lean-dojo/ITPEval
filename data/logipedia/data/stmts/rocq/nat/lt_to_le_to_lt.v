(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_le_to_lt (catalog title "nat.lt_to_le_to_lt"): transitivity from
  a strict natural-number inequality followed by a non-strict inequality.
  This file contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_to_le_to_lt :
  forall n m p : nat,
    Nat.lt n m ->
    Nat.le m p ->
    Nat.lt n p.
Admitted.
