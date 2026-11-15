-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_minus" (catalog title "nat.axiom_minus"): the source polymorphic
-- equality relates each natural-number subtraction function to the corresponding
-- naturally filtered subtraction-body function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.minus as minus
axiom minus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem axiom_minus :
    ∀ n : Nat,
      equal (Nat → Nat) (minus n)
        (filterNatType (Nat → Nat) minusBody n) := sorry

end nat
