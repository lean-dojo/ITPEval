-- Statement-only formalization of Logipedia corpus artifact
-- "nat.monotonic_le_minus_r" (catalog title "nat.monotonic_le_minus_r"):
-- natural-number subtraction from a fixed minuend reverses order in the
-- subtrahend. This file contains no proof.

theorem nat.monotonic_le_minus_r (p q n : Nat) :
    q ≤ p → n - p ≤ n - q := sorry
