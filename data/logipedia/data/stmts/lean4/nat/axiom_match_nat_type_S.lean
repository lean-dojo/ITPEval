-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_match_nat_type_S" (catalog title "nat.axiom_match_nat_type_S"):
-- the source polymorphic equality relates a natural-number eliminator at a
-- successor to the value of its successor branch. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

theorem axiom_match_nat_type_S :
    ∀ (returnType : Type) (caseO : returnType) (caseS : Nat → returnType) (n : Nat),
      equal returnType
        (matchNatType returnType caseO caseS (Nat.succ n))
        (caseS n) := sorry

end nat
