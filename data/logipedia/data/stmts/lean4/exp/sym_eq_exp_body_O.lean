-- Statement-only formalization of Logipedia corpus artifact "exp.sym_eq_exp_body_O"
-- (catalog title "exp.sym_eq_exp_body_O"): Leibniz equality relates one to the
-- exponential body at exponent zero. This file contains no proof.

namespace exp

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem sym_eq_exp_body_O :
    ∀ n : Nat, Leibniz Nat (Nat.succ 0) (expBody n 0) := sorry

end exp
