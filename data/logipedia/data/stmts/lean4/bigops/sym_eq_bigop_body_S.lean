-- Statement-only formalization of Logipedia corpus artifact "bigops.sym_eq_bigop_body_S"
-- (catalog title "bigops.sym_eq_bigop_body_S"): Leibniz equality identifies the
-- Boolean-controlled recursive step with the successor-indexed big-operation body.
-- This file contains no proof.

namespace bigops

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:bigops.bigop as bigop
axiom bigop : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

-- itpeval-source-signature: logipedia:bigops.bigop_body as bigopBody
axiom bigopBody : (H : Type) → Nat → (Nat → Bool) → H → (H → H → H) → (Nat → H) → H

theorem sym_eq_bigop_body_S :
    ∀ (H : Type) (n : Nat),
      Leibniz ((Nat → Bool) → H → (H → H → H) → (Nat → H) → H)
        (fun (p : Nat → Bool) (nil : H) (op : H → H → H) (f : Nat → H) ↦
          match p n with
          | true => op (f n) (bigop H n p nil op f)
          | false => bigop H n p nil op f)
        (bigopBody H (Nat.succ n)) := sorry

end bigops
