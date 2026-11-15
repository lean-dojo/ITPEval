-- Statement-only formalization of Logipedia corpus artifact
-- "nat.not_le_S_S_to_not_le" (catalog title "nat.not_le_S_S_to_not_le"):
-- if two successor natural numbers are not ordered, then neither are the
-- original natural numbers. This file contains no proof.

theorem nat.not_le_S_S_to_not_le (n m : Nat) :
    (¬ Nat.succ n ≤ Nat.succ m) → ¬ n ≤ m := sorry
