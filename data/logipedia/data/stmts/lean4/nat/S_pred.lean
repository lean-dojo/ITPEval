-- Statement-only formalization of Logipedia corpus artifact "nat.S_pred"
-- (catalog title "nat.S_pred"): every positive natural number is the successor
-- of its predecessor. This file contains no proof.

theorem nat.S_pred (n : Nat) : 0 < n -> Nat.succ (Nat.pred n) = n := sorry
