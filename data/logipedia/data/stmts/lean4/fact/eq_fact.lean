-- Statement-only formalization of Logipedia corpus artifact "fact.eq_fact"
-- (catalog title "fact.eq_fact"): Leibniz equality relates factorial at a
-- natural argument to the naturally filtered factorial body. This file contains no proof.

namespace fact

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:fact.fact as factFn
axiom factFn : Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

def filterNatType (R : Type) (body : Nat → R) : Nat → R
  | 0 => body 0
  | Nat.succ n => body (Nat.succ n)

theorem eq_fact :
    ∀ n : Nat, Leibniz Nat (factFn n) (filterNatType Nat factBody n) := sorry

end fact
