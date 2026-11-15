-- Statement-only formalization of Logipedia corpus artifact "nat.le_n_O_elim"
-- (catalog title "nat.le_n_O_elim"): a natural number at most zero satisfies
-- every predicate that holds at zero. This file contains no proof.

theorem nat.le_n_O_elim (n : Nat) :
    n ≤ 0 → ∀ P : Nat → Prop, P 0 → P n := sorry
