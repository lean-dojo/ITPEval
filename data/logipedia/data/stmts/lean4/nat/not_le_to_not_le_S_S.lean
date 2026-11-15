-- Statement-only formalization of Logipedia corpus artifact
-- "nat.not_le_to_not_le_S_S" (catalog title "nat.not_le_to_not_le_S_S"):
-- if one natural number is not at most another, then their successors have
-- the same failure of ordering. This file contains no proof.

theorem nat.not_le_to_not_le_S_S (n m : Nat) :
    (¬ n ≤ m) → ¬ Nat.succ n ≤ Nat.succ m := sorry
