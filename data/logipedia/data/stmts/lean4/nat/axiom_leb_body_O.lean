-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_leb_body_O" (catalog title "nat.axiom_leb_body_O"): the source
-- polymorphic equality relates the less-than-or-equal test body at zero to the
-- constant-true Boolean function on natural numbers. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.leb_body as lebBody
axiom lebBody : Nat → Nat → Bool

theorem axiom_leb_body_O :
    equal (Nat → Bool) (lebBody 0) (fun _m ↦ true) := sorry

end nat
