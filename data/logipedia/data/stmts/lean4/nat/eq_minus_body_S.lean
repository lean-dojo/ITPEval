-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_minus_body_S" (catalog title "nat.eq_minus_body_S"): Leibniz equality
-- relates the subtraction body at a successor to the natural-number eliminator
-- with that successor as its zero branch and the preceding subtraction function
-- as its successor branch. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.minus as minus
axiom minus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem eq_minus_body_S :
    ∀ n : Nat, ∀ P : (Nat → Nat) → Prop,
      P (minusBody (Nat.succ n)) →
      P (fun m ↦ matchNatType Nat (Nat.succ n) (fun q ↦ minus n q) m) := sorry

end nat
