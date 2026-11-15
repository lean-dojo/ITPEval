-- Statement-only formalization of Logipedia corpus artifact
-- "nat.not_le_to_leb_false" (catalog title "nat.not_le_to_leb_false"): if one
-- natural number is not at most another, their Boolean less-than-or-equal test
-- returns false. This file contains no proof.

theorem nat.not_le_to_leb_false (n m : Nat) :
    (¬ n ≤ m) → decide (n ≤ m) = false := sorry
