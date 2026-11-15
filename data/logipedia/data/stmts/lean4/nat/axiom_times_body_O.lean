-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_times_body_O" (catalog title "nat.axiom_times_body_O"): the source
-- polymorphic equality relates the multiplication body at zero to the constant-zero
-- function on natural numbers. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat → Nat → Nat

theorem axiom_times_body_O :
    equal (Nat → Nat) (timesBody 0) (fun _m ↦ 0) := sorry

end nat
