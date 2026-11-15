-- Statement-only formalization of Logipedia artifact "bigops.axiom_bigop_body_O":
-- the source polymorphic relation identifies the zero-indexed bigop body with the
-- operator that returns its supplied neutral element. This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:bigops.bigop_body as bigop_body
axiom bigop_body : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

theorem axiom_bigop_body_O :
    ∀ H : Type,
      equal ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (bigop_body H 0)
        (fun (_p : Nat → Bool) (nil : H) (_op : H → H → H) (_f : Nat → H) ↦ nil) := sorry

end bigops
