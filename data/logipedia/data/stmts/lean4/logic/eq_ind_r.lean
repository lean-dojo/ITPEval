-- Statement-only formalization of Logipedia corpus artifact "logic.eq_ind_r"
-- (catalog title "logic.eq_ind_r"): right-oriented equality elimination transports
-- an arbitrary predicate from an element to any element equal to it.
-- This file contains no proof.

theorem logic.eq_ind_r (A : Type) (a : A) (P : A → Prop) :
    P a → ∀ x : A, x = a → P x := sorry
