-- Statement-only formalization of Logipedia corpus artifact "nat.eqb_false_to_not_eq"
-- (catalog title "nat.eqb_false_to_not_eq"): a false Boolean equality test for
-- two natural numbers implies that the numbers are unequal. This file contains no proof.

theorem nat.eqb_false_to_not_eq (n m : Nat) :
    decide (n = m) = false → n ≠ m := sorry
