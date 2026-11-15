-- Statement-only formalization of Logipedia corpus artifact "nat.lt_plus_Sn_r"
-- (catalog title "nat.lt_plus_Sn_r"): for all natural numbers a, x, and n,
-- a is strictly less than (a + x) plus the successor of n. This file contains no proof.

theorem nat.lt_plus_Sn_r (a x n : Nat) :
    a < (a + x) + Nat.succ n := sorry
