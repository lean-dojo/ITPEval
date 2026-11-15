-- Statement-only formalization of Logipedia corpus artifact "logic.eq_rect_r"
-- (catalog title "logic.eq_rect_r"): equality transport along x = a carries an
-- arbitrary predicate from a to x. This file contains no proof.

theorem logic.eq_rect_r (A : Type) (a x : A) :
    x = a → ∀ P : A → Prop, P a → P x := sorry
