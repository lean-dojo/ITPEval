-- Statement-only formalization of Logipedia corpus artifact "nat.le_gen"
-- (catalog title "nat.le_gen"): if a predicate holds for every natural number
-- at most a given natural number, then it holds for that number. This file contains no proof.

theorem nat.le_gen (P : Nat → Prop) (n : Nat) :
    (∀ i : Nat, i ≤ n → P i) → P n := sorry
