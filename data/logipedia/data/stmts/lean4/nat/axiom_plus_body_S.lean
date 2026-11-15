-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_plus_body_S" (catalog title "nat.axiom_plus_body_S"): the source
-- polymorphic equality relates the addition body at a successor to the
-- successor of the preceding addition function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.plus as plus
axiom plus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.plus_body as plusBody
axiom plusBody : Nat → Nat → Nat

theorem axiom_plus_body_S :
    ∀ n : Nat,
      equal (Nat → Nat) (plusBody (Nat.succ n))
        (fun m ↦ Nat.succ (plus n m)) := sorry

end nat
