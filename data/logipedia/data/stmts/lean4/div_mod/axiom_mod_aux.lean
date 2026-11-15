-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.axiom_mod_aux" (catalog title "div_mod.axiom_mod_aux"): the source
-- polymorphic equality relates each modulus auxiliary function to the corresponding
-- naturally filtered modulus body function. This file contains no proof.

namespace div_mod

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:div_mod.mod_aux as modAux
axiom modAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:div_mod.mod_aux_body as modAuxBody
axiom modAuxBody : Nat → Nat → Nat → Nat

theorem axiom_mod_aux :
    ∀ p : Nat,
      equal (Nat → Nat → Nat) (modAux p)
        (filterNatType (Nat → Nat → Nat) modAuxBody p) := sorry

end div_mod
