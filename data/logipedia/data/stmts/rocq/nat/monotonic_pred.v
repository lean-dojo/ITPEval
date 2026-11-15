(*
  Statement-only formalization of Logipedia corpus artifact
  nat.monotonic_pred (catalog title "nat.monotonic_pred"): the predecessor
  function is monotone with respect to natural-number order. This file
  contains no proof.
*)

From Stdlib Require Import Arith.PeanoNat.

Theorem logipedia_nat_monotonic_pred :
  forall n m : nat,
    n <= m ->
    Nat.pred n <= Nat.pred m.
Admitted.
