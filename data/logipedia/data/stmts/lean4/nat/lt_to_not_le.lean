-- Statement-only formalization of Logipedia corpus artifact "nat.lt_to_not_le"
-- (catalog title "nat.lt_to_not_le"): strict inequality between natural
-- numbers implies that the larger number is not less than or equal to the
-- smaller one. This file contains no proof.

theorem nat.lt_to_not_le (n m : Nat) : n < m → ¬m ≤ n := sorry
