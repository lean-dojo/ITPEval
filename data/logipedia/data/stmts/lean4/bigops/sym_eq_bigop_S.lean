-- Statement-only formalization of Logipedia corpus artifact "bigops.sym_eq_bigop_S"
-- (catalog title "bigops.sym_eq_bigop_S"): Leibniz equality at a successor index
-- from the polymorphic big-operation body to the big-operation function.
-- This file contains no proof.

namespace bigops

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:bigops.bigop as bigop
axiom bigop : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

-- itpeval-source-signature: logipedia:bigops.bigop_body as bigopBody
axiom bigopBody : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

theorem sym_eq_bigop_S :
    ∀ (H : Type) (n : Nat),
      Leibniz ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (bigopBody H (Nat.succ n)) (bigop H (Nat.succ n)) := sorry

end bigops
