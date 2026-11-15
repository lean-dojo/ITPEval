-- Statement-only formalization of Logipedia corpus artifact
-- "exp.axiom_exp_body_O" (catalog title "exp.axiom_exp_body_O"): the source
-- polymorphic equality relates the exponential body at exponent zero to one.
-- This file contains no proof.

namespace exp

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem axiom_exp_body_O :
    ∀ n : Nat, equal Nat (expBody n 0) (Nat.succ 0) := sorry

end exp
