-- Statement-only formalization of Logipedia corpus artifact "exp.eq_exp_body_O"
-- (catalog title "exp.eq_exp_body_O"): Leibniz equality relates the exponential
-- body at exponent zero to one. This file contains no proof.

namespace exp

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem eq_exp_body_O :
    ∀ n : Nat, Leibniz Nat (expBody n 0) (Nat.succ 0) := sorry

end exp
