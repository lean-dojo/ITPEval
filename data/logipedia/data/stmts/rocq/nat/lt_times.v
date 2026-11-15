(*
  Statement-only formalization of Logipedia corpus artifact nat.lt_times
  (catalog title "nat.lt_times"): strict inequalities between two pairs of
  natural numbers imply a strict inequality between their products. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_lt_times :
  forall n m p q : nat,
    n < m ->
    p < q ->
    Nat.mul n p < Nat.mul m q.
Admitted.
