-- Statement-only formalization of Logipedia corpus artifact "nat.lt_O_n_elim"
-- (catalog title "nat.lt_O_n_elim"): a positive natural number satisfies every
-- predicate that holds for all successor natural numbers. This file contains no proof.

theorem nat.lt_O_n_elim (n : Nat) :
    0 < n → ∀ P : Nat → Prop, (∀ m : Nat, P (Nat.succ m)) → P n := sorry
