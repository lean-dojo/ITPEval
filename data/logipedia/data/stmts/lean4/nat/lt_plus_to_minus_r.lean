-- Statement-only formalization of Logipedia corpus artifact "nat.lt_plus_to_minus_r"
-- (catalog title "nat.lt_plus_to_minus_r"): if the sum of two natural numbers is
-- strictly below a third, the first is below the third minus the second.
-- This file contains no proof.

theorem nat.lt_plus_to_minus_r (a b c : Nat) :
    a + b < c → a < c - b := sorry
