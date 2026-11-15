-- Statement-only formalization of Logipedia corpus artifact
-- "nat.lt_to_le_to_lt" (catalog title "nat.lt_to_le_to_lt"): if one natural
-- number is less than a second and the second is at most a third, then the first
-- is less than the third. This file contains no proof.

theorem nat.lt_to_le_to_lt (n m p : Nat) :
    n < m → m ≤ p → n < p := sorry
