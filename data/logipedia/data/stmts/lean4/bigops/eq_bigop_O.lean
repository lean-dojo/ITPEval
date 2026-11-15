-- Statement-only formalization of Logipedia corpus artifact "bigops.eq_bigop_O"
-- (catalog title "bigops.eq_bigop_O"): Leibniz equality at index zero between
-- the polymorphic big-operation function and its body. This file contains no proof.

namespace bigops

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:bigops.bigop as bigop
axiom bigop : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

-- itpeval-source-signature: logipedia:bigops.bigop_body as bigop_body
axiom bigop_body : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

theorem eq_bigop_O :
    ∀ H : Type,
      Leibniz ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (bigop H 0) (bigop_body H 0) := sorry

end bigops
