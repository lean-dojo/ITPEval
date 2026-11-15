-- Statement-only formalization of Logipedia corpus artifact
-- "nat.monotonic_lt_times_r" (catalog title "nat.monotonic_lt_times_r"):
-- left multiplication by a positive natural number is strictly monotone.
-- This file contains no proof.

theorem nat.monotonic_lt_times_r :
    ∀ c : Nat, 0 < c → ∀ x y : Nat, x < y → c * x < c * y := sorry
