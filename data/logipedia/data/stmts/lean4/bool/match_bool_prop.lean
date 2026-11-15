-- Statement-only formalization of Logipedia corpus artifact "bool.match_bool_prop"
-- (catalog title "bool.match_bool_prop"): a predicate holding for both Boolean values
-- holds for every Boolean. This file contains no proof.

theorem bool.match_bool_prop
    (return_ : Bool → Prop)
    (caseTrue : return_ true)
    (caseFalse : return_ false) :
    ∀ z : Bool, return_ z := sorry
