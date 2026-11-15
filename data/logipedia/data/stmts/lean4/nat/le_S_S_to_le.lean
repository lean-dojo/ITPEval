-- Statement-only formalization of Logipedia corpus artifact "nat.le_S_S_to_le"
-- (catalog title "nat.le_S_S_to_le"): if the successors of two natural numbers
-- are ordered, then the original numbers have the same ordering. This file contains no proof.

theorem nat.le_S_S_to_le (n m : Nat) :
    Nat.succ n ≤ Nat.succ m → n ≤ m := sorry
