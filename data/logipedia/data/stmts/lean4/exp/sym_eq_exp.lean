-- Statement-only formalization of Logipedia corpus artifact "exp.sym_eq_exp"
-- (catalog title "exp.sym_eq_exp"): Leibniz equality relates the naturally
-- filtered exponentiation body at two natural arguments to exponentiation.
-- This file contains no proof.

namespace exp

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

def filterNatType (R : Type) (body : Nat → R) : Nat → R
  | 0 => body 0
  | Nat.succ n => body (Nat.succ n)

-- itpeval-source-signature: logipedia:exp.exp as expFn
axiom expFn : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem sym_eq_exp :
    ∀ (n m : Nat),
      Leibniz Nat (filterNatType Nat (expBody n) m) (expFn n m) := sorry

end exp
