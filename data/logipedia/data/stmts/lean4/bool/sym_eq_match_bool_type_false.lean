-- Statement-only formalization of Logipedia corpus artifact
-- "bool.sym_eq_match_bool_type_false" (catalog title
-- "bool.sym_eq_match_bool_type_false"): the false-branch value equals the
-- result of a polymorphic Boolean match at false. This file contains no proof.

theorem bool.sym_eq_match_bool_type_false :
    ∀ (A : Type) (caseTrue caseFalse : A),
      caseFalse =
        match false with
        | true => caseTrue
        | false => caseFalse := sorry
