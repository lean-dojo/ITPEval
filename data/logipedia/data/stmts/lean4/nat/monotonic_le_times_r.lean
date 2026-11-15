-- Statement-only formalization of Logipedia corpus artifact
-- "nat.monotonic_le_times_r" (catalog title "nat.monotonic_le_times_r"):
-- multiplication by a fixed natural number on the left preserves
-- natural-number order in the right factor. This file contains no proof.

theorem nat.monotonic_le_times_r (n x y : Nat) :
    x ≤ y → n * x ≤ n * y := sorry
