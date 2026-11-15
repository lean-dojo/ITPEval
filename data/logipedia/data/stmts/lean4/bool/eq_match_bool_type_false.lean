-- Statement-only formalization of Logipedia corpus artifact
-- "bool.eq_match_bool_type_false" (catalog title
-- "bool.eq_match_bool_type_false"): a polymorphic Boolean match at false equals
-- its false-branch value. This file contains no proof.

theorem bool.eq_match_bool_type_false :
    ∀ (A : Type) (caseTrue caseFalse : A),
      (match false with
        | true => caseTrue
        | false => caseFalse) = caseFalse := sorry
