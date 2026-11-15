-- Statement-only formalization of Logipedia corpus artifact "nat.le_to_le_to_eq"
-- (catalog title "nat.le_to_le_to_eq"): two natural numbers are equal if each
-- is less than or equal to the other. This file contains no proof.

theorem nat.le_to_le_to_eq (n m : Nat) :
    n ≤ m → m ≤ n → n = m := sorry
