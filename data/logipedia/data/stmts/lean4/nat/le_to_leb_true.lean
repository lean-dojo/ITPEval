-- Statement-only formalization of Logipedia corpus artifact "nat.le_to_leb_true"
-- (catalog title "nat.le_to_leb_true"): an order relation between two natural
-- numbers implies that their Boolean less-than-or-equal test returns true.
-- This file contains no proof.

theorem nat.le_to_leb_true (n m : Nat) :
    n ≤ m → decide (n ≤ m) = true := sorry
