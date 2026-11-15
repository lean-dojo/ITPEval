-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.axiom_div_aux_body_S" (catalog title "div_mod.axiom_div_aux_body_S"):
-- the source polymorphic equality relates each successor-indexed division auxiliary
-- body to its Boolean-controlled recursive quotient step. This file contains no proof.

namespace div_mod

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:div_mod.div_aux as divAux
axiom divAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:div_mod.div_aux_body as divAuxBody
axiom divAuxBody : Nat → Nat → Nat → Nat

theorem axiom_div_aux_body_S :
    ∀ p : Nat,
      equal (Nat → Nat → Nat) (divAuxBody (Nat.succ p))
        (fun (m n : Nat) ↦
          if m ≤ n then 0
          else Nat.succ (divAux p (m - Nat.succ n) n)) := sorry

end div_mod
