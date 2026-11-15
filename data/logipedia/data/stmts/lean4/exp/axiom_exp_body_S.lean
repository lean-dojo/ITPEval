-- Statement-only formalization of Logipedia corpus artifact
-- "exp.axiom_exp_body_S" (catalog title "exp.axiom_exp_body_S"): the source
-- polymorphic equality relates the exponential body at a successor exponent
-- to the product of exponentiation at the preceding exponent and its base.
-- This file contains no proof.

namespace exp

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:exp.exp as expFn
axiom expFn : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem axiom_exp_body_S :
    ∀ (n m : Nat),
      equal Nat (expBody n (Nat.succ m)) (times (expFn n m) n) := sorry

end exp
