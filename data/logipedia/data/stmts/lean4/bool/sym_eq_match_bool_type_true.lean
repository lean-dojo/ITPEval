-- Statement-only formalization of Logipedia corpus artifact
-- "bool.sym_eq_match_bool_type_true" (catalog title
-- "bool.sym_eq_match_bool_type_true"): the true-branch value equals the
-- result of a polymorphic Boolean match at true. This file contains no proof.

theorem bool.sym_eq_match_bool_type_true :
    ∀ (A : Type) (caseTrue caseFalse : A),
      caseTrue =
        match true with
        | true => caseTrue
        | false => caseFalse := sorry
