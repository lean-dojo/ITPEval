-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_minus_body_O" (catalog title "nat.axiom_minus_body_O"): the source
-- polymorphic equality relates the subtraction body at zero to the constant-zero
-- function on natural numbers. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem axiom_minus_body_O :
    equal (Nat → Nat) (minusBody 0) (fun _m ↦ 0) := sorry

end nat
