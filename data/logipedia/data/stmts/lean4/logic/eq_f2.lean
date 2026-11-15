-- Statement-only formalization of Logipedia corpus artifact "logic.eq_f2"
-- (catalog title "logic.eq_f2"): equality is preserved when an arbitrary
-- binary function is applied to equal inputs. This file contains no proof.

theorem logic.eq_f2
    (A B C : Type)
    (f : A → B → C)
    (x1 x2 : A)
    (y1 y2 : B) :
    x1 = x2 → y1 = y2 → f x1 y1 = f x2 y2 := sorry
