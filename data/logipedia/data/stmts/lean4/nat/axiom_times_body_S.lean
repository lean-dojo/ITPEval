-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_times_body_S" (catalog title "nat.axiom_times_body_S"): the source
-- polymorphic equality relates the multiplication body at a successor to the
-- function adding its argument to multiplication at the predecessor.
-- This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.plus as plus
axiom plus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat → Nat → Nat

theorem axiom_times_body_S :
    ∀ n : Nat,
      equal (Nat → Nat) (timesBody (Nat.succ n))
        (fun m ↦ plus m (times n m)) := sorry

end nat
