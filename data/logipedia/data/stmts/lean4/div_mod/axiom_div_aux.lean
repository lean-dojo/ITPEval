-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.axiom_div_aux" (catalog title "div_mod.axiom_div_aux"): the source
-- polymorphic equality relates each division auxiliary function to the corresponding
-- naturally filtered division body function. This file contains no proof.

namespace div_mod

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

def filterNatType (R : Type) (body : Nat → R) : Nat → R
  | 0 => body 0
  | Nat.succ n => body (Nat.succ n)

-- itpeval-source-signature: logipedia:div_mod.div_aux as divAux
axiom divAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:div_mod.div_aux_body as divAuxBody
axiom divAuxBody : Nat → Nat → Nat → Nat

theorem axiom_div_aux :
    ∀ p : Nat,
      sourceEqual (Nat → Nat → Nat) (divAux p)
        (filterNatType (Nat → Nat → Nat) divAuxBody p) := sorry

end div_mod
