-- Statement-only formalization of Logipedia corpus artifact
-- "nat.le_to_lt_to_lt" (catalog title "nat.le_to_lt_to_lt"): if one natural
-- number is at most a second and the second is less than a third, then the
-- first is less than the third. This file contains no proof.

theorem nat.le_to_lt_to_lt (n m p : Nat) :
    n ≤ m → m < p → n < p := sorry
