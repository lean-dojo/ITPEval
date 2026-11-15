-- Statement-only formalization of Logipedia corpus artifact
-- "nat.lt_to_le_to_lt_times" (catalog title "nat.lt_to_le_to_lt_times"):
-- if n is less than m, p is at most q, and q is positive, then n * p is
-- less than m * q for natural numbers. This file contains no proof.

theorem nat.lt_to_le_to_lt_times (n m p q : Nat) :
    n < m → p ≤ q → 0 < q → n * p < m * q := sorry
