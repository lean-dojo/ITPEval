-- Statement-only formalization of Logipedia corpus artifact "nat.eqb_true_to_eq"
-- (catalog title "nat.eqb_true_to_eq"): a true Boolean equality test for
-- two natural numbers implies that the numbers are equal. This file contains no proof.

theorem nat.eqb_true_to_eq (n m : Nat) :
    decide (n = m) = true → n = m := sorry
