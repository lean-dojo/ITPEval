-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_filter_nat_type_S" (catalog title "nat.axiom_filter_nat_type_S"):
-- the source polymorphic equality relates filtering any natural-indexed function
-- at a successor to applying that function at the same successor. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

theorem axiom_filter_nat_type_S :
    ∀ (returnType : Type) (returnFn : Nat → returnType) (n : Nat),
      equal returnType
        (filterNatType returnType returnFn (Nat.succ n))
        (returnFn (Nat.succ n)) := sorry

end nat
