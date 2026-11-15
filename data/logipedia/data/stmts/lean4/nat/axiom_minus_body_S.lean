-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_minus_body_S" (catalog title "nat.axiom_minus_body_S"): the source
-- polymorphic equality relates the subtraction body at a successor to the
-- natural-number eliminator with that successor as its zero branch and the
-- preceding subtraction function as its successor branch. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.minus as minus
axiom minus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem axiom_minus_body_S :
    ∀ n : Nat,
      equal (Nat → Nat) (minusBody (Nat.succ n))
        (fun m ↦ matchNatType Nat (Nat.succ n) (fun q ↦ minus n q) m) := sorry

end nat
