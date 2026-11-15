-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.axiom_mod_aux_body_O" (catalog title "div_mod.axiom_mod_aux_body_O"):
-- the source polymorphic equality relates the zero-indexed modulus auxiliary body
-- to the binary natural-number function returning its first argument. This file contains no proof.

namespace div_mod

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:div_mod.mod_aux_body as modAuxBody
axiom modAuxBody : Nat → Nat → Nat → Nat

theorem axiom_mod_aux_body_O :
    equal (Nat → Nat → Nat) (modAuxBody 0) (fun (m _n : Nat) ↦ m) := sorry

end div_mod
