-- Statement-only formalization of Logipedia artifact "bigops.axiom_bigop_S":
-- equality under the source's polymorphic relation of the successor-indexed bigop
-- and bigop_body operator families. This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:bigops.bigop as bigop
axiom bigop : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

-- itpeval-source-signature: logipedia:bigops.bigop_body as bigop_body
axiom bigop_body : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

theorem axiom_bigop_S :
    ∀ (H : Type) (n : Nat),
      equal ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (bigop H (Nat.succ n)) (bigop_body H (Nat.succ n)) := sorry

end bigops
