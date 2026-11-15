-- Statement-only formalization of Logipedia corpus artifact "logic.rewrite_l"
-- (catalog title "logic.rewrite_l"): left-oriented equality rewriting transports
-- an arbitrary predicate from x to an equal y. This file contains no proof.

theorem logic.rewrite_l (A : Type) (x : A) (P : A → Prop) :
    P x → ∀ y : A, x = y → P y := sorry
