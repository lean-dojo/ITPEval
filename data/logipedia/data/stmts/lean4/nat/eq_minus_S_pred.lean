-- Statement-only formalization of Logipedia corpus artifact "nat.eq_minus_S_pred"
-- (catalog title "nat.eq_minus_S_pred"): for all natural numbers n and m,
-- subtracting the successor of m from n equals the predecessor of n minus m.
-- This file contains no proof.

theorem nat.eq_minus_S_pred (n m : Nat) :
    n - Nat.succ m = Nat.pred (n - m) := sorry
