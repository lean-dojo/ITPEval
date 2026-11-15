-- Statement-only formalization of Logipedia corpus artifact "nat.le_plus_to_minus"
-- (catalog title "nat.le_plus_to_minus"): a natural number bounded by p + m
-- remains bounded by p after truncated subtraction of m. This file contains no proof.

theorem nat.le_plus_to_minus (n m p : Nat) :
    n ≤ p + m → n - m ≤ p := sorry
