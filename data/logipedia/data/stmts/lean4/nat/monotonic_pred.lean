-- Statement-only formalization of Logipedia corpus artifact "nat.monotonic_pred"
-- (catalog title "nat.monotonic_pred"): the predecessor function preserves
-- natural-number order. This file contains no proof.

theorem nat.monotonic_pred (n m : Nat) :
    n ≤ m → Nat.pred n ≤ Nat.pred m := sorry
