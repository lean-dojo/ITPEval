-- Statement-only formalization of Logipedia corpus artifact
-- "nat.monotonic_le_plus_l" (catalog title "nat.monotonic_le_plus_l"):
-- addition of a fixed natural number on the right preserves natural-number
-- order. This file contains no proof.

theorem nat.monotonic_le_plus_l (m x y : Nat) :
    x ≤ y → x + m ≤ y + m := sorry
