-- Statement-only formalization of Logipedia corpus artifact "logic.rewrite_r"
-- (catalog title "logic.rewrite_r"): right-oriented equality rewriting transports
-- an arbitrary predicate from x to an equal y. This file contains no proof.

theorem logic.rewrite_r (A : Type) (x : A) (P : A → Prop) :
    P x → ∀ y : A, y = x → P y := sorry
