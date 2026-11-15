-- Statement-only formalization of Logipedia corpus artifact
-- "bool.axiom_match_bool_type_false" (catalog title
-- "bool.axiom_match_bool_type_false"): the source polymorphic equality relates
-- a Boolean eliminator at false to its false-branch value. This file contains no proof.

namespace bool

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

def matchBoolType (A : Type) (caseTrue caseFalse : A) : Bool → A
  | true => caseTrue
  | false => caseFalse

theorem axiom_match_bool_type_false :
    ∀ (A : Type) (caseTrue caseFalse : A),
      sourceEqual A (matchBoolType A caseTrue caseFalse false) caseFalse := sorry

end bool
