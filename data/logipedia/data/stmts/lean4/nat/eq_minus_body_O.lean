-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_minus_body_O" (catalog title "nat.eq_minus_body_O"): Leibniz equality
-- relates the subtraction body at zero to the constant-zero function on natural
-- numbers. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat → Nat → Nat

theorem eq_minus_body_O :
    ∀ P : (Nat → Nat) → Prop,
      P (minusBody 0) →
      P (fun _m ↦ 0) := sorry

end nat
