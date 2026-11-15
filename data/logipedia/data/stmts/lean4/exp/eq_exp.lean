-- Statement-only formalization of Logipedia corpus artifact "exp.eq_exp"
-- (catalog title "exp.eq_exp"): Leibniz equality relates exponentiation at
-- two natural arguments to the naturally filtered exponentiation body.
-- This file contains no proof.

namespace exp

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:exp.exp as expFn
axiom expFn : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem eq_exp :
    ∀ (n m : Nat),
      Leibniz Nat (expFn n m) (filterNatType Nat (expBody n) m) := sorry

end exp
