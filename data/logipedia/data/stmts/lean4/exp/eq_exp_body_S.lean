-- Statement-only formalization of Logipedia corpus artifact "exp.eq_exp_body_S"
-- (catalog title "exp.eq_exp_body_S"): Leibniz equality relates the exponential
-- body at a successor exponent to the product of exponentiation at the preceding
-- exponent and its base. This file contains no proof.

namespace exp

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:exp.exp as expFn
axiom expFn : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem eq_exp_body_S :
    ∀ (n m : Nat),
      Leibniz Nat (expBody n (Nat.succ m)) (expFn n m * n) := sorry

end exp
