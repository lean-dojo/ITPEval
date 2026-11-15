-- Statement-only formalization of Logipedia corpus artifact
-- "nat.minus_minus" (catalog title "nat.minus_minus"): for natural numbers
-- p <= m <= n, truncated subtraction satisfies p + (n - m) = n - (m - p).
-- This file contains no proof.

theorem nat.minus_minus (n m p : Nat) :
    p ≤ m → m ≤ n → p + (n - m) = n - (m - p) := sorry
