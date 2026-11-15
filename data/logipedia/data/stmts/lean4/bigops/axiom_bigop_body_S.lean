-- Statement-only formalization of Logipedia artifact "bigops.axiom_bigop_body_S":
-- the successor-indexed bigop body is related at its full curried function type to
-- the Boolean-controlled step using the preceding bigop. This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:bigops.bigop as bigop
axiom bigop : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

-- itpeval-source-signature: logipedia:bigops.bigop_body as bigopBody
axiom bigopBody : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

theorem axiom_bigop_body_S :
    ∀ (H : Type) (n : Nat),
      sourceEqual ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (bigopBody H (Nat.succ n))
        (fun (p : Nat → Bool) (nil : H) (op : H → H → H) (f : Nat → H) ↦
          match p n with
          | true => op (f n) (bigop H n p nil op f)
          | false => bigop H n p nil op f) := sorry

end bigops
