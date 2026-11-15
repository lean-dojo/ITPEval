-- Statement-only formalization of Logipedia corpus artifact "nat.eq_minus"
-- (catalog title "nat.eq_minus"): each partially applied natural-number subtraction
-- function is Leibniz-equal to its naturally filtered body. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.minus as minus
axiom minus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem eq_minus :
    ∀ n : Nat, ∀ P : (Nat → Nat) → Prop,
      P (minus n) →
      P (filterNatType (Nat → Nat) minusBody n) := sorry

end nat
