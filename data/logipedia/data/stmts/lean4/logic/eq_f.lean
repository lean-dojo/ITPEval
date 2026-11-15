-- Statement-only formalization of Logipedia corpus artifact "logic.eq_f"
-- (catalog title "logic.eq_f"): equality is preserved by every function between
-- arbitrary types. This file contains no proof.

theorem logic.eq_f (A B : Type) (f : A → B) (x y : A) :
    x = y → f x = f y := sorry
