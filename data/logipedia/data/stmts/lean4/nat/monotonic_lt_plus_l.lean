-- Statement-only formalization of Logipedia corpus artifact "nat.monotonic_lt_plus_l"
-- (catalog title "nat.monotonic_lt_plus_l"): for every natural number, adding it
-- on the right is strictly monotone. This file contains no proof.

theorem nat.monotonic_lt_plus_l :
    ∀ n x y : Nat, x < y → x + n < y + n := sorry
