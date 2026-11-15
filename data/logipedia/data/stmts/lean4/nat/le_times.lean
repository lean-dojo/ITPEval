-- Statement-only formalization of Logipedia corpus artifact "nat.le_times"
-- (catalog title "nat.le_times"): natural-number multiplication preserves the
-- order relation componentwise. This file contains no proof.

theorem nat.le_times (n1 n2 m1 m2 : Nat) :
    n1 ≤ n2 → m1 ≤ m2 → n1 * m1 ≤ n2 * m2 := sorry
