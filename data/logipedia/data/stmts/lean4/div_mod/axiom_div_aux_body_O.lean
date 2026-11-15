-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.axiom_div_aux_body_O" (catalog title "div_mod.axiom_div_aux_body_O"):
-- the source polymorphic equality relates the zero-indexed division auxiliary body
-- to the constant-zero binary natural-number function. This file contains no proof.

namespace div_mod

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:div_mod.div_aux_body as divAuxBody
axiom divAuxBody : Nat → Nat → Nat → Nat

theorem axiom_div_aux_body_O :
    sourceEqual (Nat → Nat → Nat) (divAuxBody 0)
      (fun (_m _n : Nat) ↦ 0) := sorry

end div_mod
