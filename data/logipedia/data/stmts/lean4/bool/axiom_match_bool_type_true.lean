-- Statement-only formalization of Logipedia corpus artifact
-- "bool.axiom_match_bool_type_true" (catalog title
-- "bool.axiom_match_bool_type_true"): the source polymorphic equality relates
-- a Boolean eliminator at true to its true-branch value. This file contains no proof.

namespace bool

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:bool.match_bool_type as matchBoolType
axiom matchBoolType : (A : Type) → A → A → Bool → A

theorem axiom_match_bool_type_true :
    ∀ (A : Type) (caseTrue caseFalse : A),
      equal A (matchBoolType A caseTrue caseFalse true) caseTrue := sorry

end bool
