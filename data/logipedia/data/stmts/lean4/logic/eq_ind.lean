-- Statement-only formalization of Logipedia corpus artifact "logic.eq_ind"
-- (catalog title "logic.eq_ind"): equality elimination transports an arbitrary
-- predicate from an element to any equal element. This file contains no proof.

theorem logic.eq_ind (A : Type) (x : A) (P : A → Prop) :
    P x → ∀ y : A, x = y → P y := sorry
