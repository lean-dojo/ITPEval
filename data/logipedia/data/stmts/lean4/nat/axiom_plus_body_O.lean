-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_plus_body_O" (catalog title "nat.axiom_plus_body_O"): the source
-- polymorphic equality relates the addition body at zero to the identity function
-- on natural numbers. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.plus_body as plusBody
axiom plusBody : Nat → Nat → Nat

theorem axiom_plus_body_O :
    equal (Nat → Nat) (plusBody 0) (fun m ↦ m) := sorry

end nat
