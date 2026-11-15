-- Statement-only formalization of Logipedia corpus artifact
-- "bool.eq_match_bool_type_true" (catalog title
-- "bool.eq_match_bool_type_true"): a polymorphic Boolean match at true equals
-- its true-branch value. This file contains no proof.

theorem bool.eq_match_bool_type_true :
    ∀ (A : Type) (caseTrue caseFalse : A),
      (match true with
        | true => caseTrue
        | false => caseFalse) = caseTrue := sorry
