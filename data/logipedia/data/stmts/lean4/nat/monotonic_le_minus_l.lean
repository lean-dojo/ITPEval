-- Statement-only formalization of Logipedia corpus artifact
-- "nat.monotonic_le_minus_l" (catalog title "nat.monotonic_le_minus_l"):
-- truncated subtraction by a fixed natural number preserves the order between
-- two natural numbers. This file contains no proof.

theorem nat.monotonic_le_minus_l (p q n : Nat) :
    q ≤ p → q - n ≤ p - n := sorry
