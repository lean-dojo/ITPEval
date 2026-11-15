-- Statement-only formalization of Logipedia corpus artifact "nat.not_lt_to_le"
-- (catalog title "nat.not_lt_to_le"): for natural numbers, failure of n < m
-- implies m ≤ n. This file contains no proof.

theorem nat.not_lt_to_le (n m : Nat) : (¬ n < m) → m ≤ n := sorry
