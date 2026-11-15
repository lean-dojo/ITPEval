-- Statement-only formalization of Logipedia corpus artifact "nat.eq_to_eqb_true"
-- (catalog title "nat.eq_to_eqb_true"): equality of two natural numbers implies
-- that their Boolean equality test returns true. This file contains no proof.

theorem nat.eq_to_eqb_true (n m : Nat) :
    n = m → decide (n = m) = true := sorry
