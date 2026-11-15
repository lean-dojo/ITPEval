-- Statement-only formalization of Logipedia corpus artifact "nat.not_le_to_lt"
-- (catalog title "nat.not_le_to_lt"): for natural numbers, failure of n ≤ m
-- implies m < n. This file contains no proof.

theorem nat.not_le_to_lt (n m : Nat) : (¬ n ≤ m) → m < n := sorry
