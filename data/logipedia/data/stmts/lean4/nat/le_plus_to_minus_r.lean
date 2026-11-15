-- Statement-only formalization of Logipedia corpus artifact "nat.le_plus_to_minus_r"
-- (catalog title "nat.le_plus_to_minus_r"): if the sum of natural numbers a and b
-- is at most c, then a is at most c minus b using truncated subtraction. This file
-- contains no proof.

theorem nat.le_plus_to_minus_r (a b c : Nat) :
    a + b ≤ c → a ≤ c - b := sorry
