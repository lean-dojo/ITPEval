-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.axiom_mod_aux_body_S" (catalog title "div_mod.axiom_mod_aux_body_S"):
-- the source polymorphic equality relates each successor-indexed modulus auxiliary
-- body to its Boolean-controlled recursive remainder step. This file contains no proof.

namespace div_mod

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:div_mod.mod_aux as modAux
axiom modAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:div_mod.mod_aux_body as modAuxBody
axiom modAuxBody : Nat → Nat → Nat → Nat

theorem axiom_mod_aux_body_S :
    ∀ p : Nat,
      sourceEqual (Nat → Nat → Nat) (modAuxBody (Nat.succ p))
        (fun (m n : Nat) ↦
          if m ≤ n then m
          else modAux p (m - Nat.succ n) n) := sorry

end div_mod
