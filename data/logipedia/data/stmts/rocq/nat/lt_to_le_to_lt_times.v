(*
  Statement-only formalization of Logipedia corpus artifact
  nat.lt_to_le_to_lt_times (catalog title "nat.lt_to_le_to_lt_times"):
  multiplying a strict natural-number inequality and a non-strict one, with
  a positive upper factor, yields a strict product inequality. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_to_le_to_lt_times :
  forall n m p q : nat,
    n < m ->
    p <= q ->
    0 < q ->
    Nat.mul n p < Nat.mul m q.
Admitted.
