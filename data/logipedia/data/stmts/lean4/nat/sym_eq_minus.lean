-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_minus"
-- (catalog title "nat.sym_eq_minus"): each naturally filtered natural-number
-- subtraction-body function is Leibniz-equal to the corresponding partially
-- applied subtraction function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.minus as minus
axiom minus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem sym_eq_minus :
    ∀ n : Nat, ∀ P : (Nat → Nat) → Prop,
      P (filterNatType (Nat → Nat) minusBody n) →
      P (minus n) := sorry

end nat
