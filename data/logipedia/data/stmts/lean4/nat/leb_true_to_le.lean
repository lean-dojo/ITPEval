-- Statement-only formalization of Logipedia corpus artifact "nat.leb_true_to_le"
-- (catalog title "nat.leb_true_to_le"): a true Boolean less-than-or-equal test
-- for two natural numbers implies that the first is at most the second.
-- This file contains no proof.

theorem nat.leb_true_to_le (n m : Nat) :
    decide (n ≤ m) = true → n ≤ m := sorry
