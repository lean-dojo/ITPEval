-- Statement-only formalization of Logipedia corpus artifact "nat.not_eq_to_eqb_false"
-- (catalog title "nat.not_eq_to_eqb_false"): inequality of two natural numbers implies
-- that their Boolean equality test returns false. This file contains no proof.

theorem nat.not_eq_to_eqb_false (n m : Nat) :
    n ≠ m → decide (n = m) = false := sorry
