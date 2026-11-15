-- Statement-only formalization of Logipedia corpus artifact
-- "nat.monotonic_lt_times_l" (catalog title "nat.monotonic_lt_times_l"):
-- right multiplication by a positive natural number is strictly monotone.
-- This file contains no proof.

theorem nat.monotonic_lt_times_l :
    ∀ c : Nat, 0 < c → ∀ x y : Nat, x < y → x * c < y * c := sorry
