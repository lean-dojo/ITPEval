-- Statement-only formalization of Logipedia corpus artifact "nat.le_S_S"
-- (catalog title "nat.le_S_S"): if one natural number is at most another,
-- then their successors have the same ordering. This file contains no proof.

theorem nat.le_S_S (n m : Nat) :
    n ≤ m → Nat.succ n ≤ Nat.succ m := sorry
