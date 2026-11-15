-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_match_nat_type_O" (catalog title "nat.axiom_match_nat_type_O"):
-- the source polymorphic equality relates a natural-number eliminator at zero
-- to its zero-branch value. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

theorem axiom_match_nat_type_O :
    ∀ (returnType : Type) (caseO : returnType) (caseS : Nat → returnType),
      equal returnType (matchNatType returnType caseO caseS 0) caseO := sorry

end nat
