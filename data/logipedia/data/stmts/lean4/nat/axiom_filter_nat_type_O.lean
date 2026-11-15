-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_filter_nat_type_O" (catalog title "nat.axiom_filter_nat_type_O"):
-- the source polymorphic equality relates filtering any natural-indexed function
-- at zero to applying that function at zero. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

theorem axiom_filter_nat_type_O :
    ∀ (returnType : Type) (returnFn : Nat → returnType),
      equal returnType (filterNatType returnType returnFn 0) (returnFn 0) := sorry

end nat
