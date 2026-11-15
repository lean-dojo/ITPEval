-- Statement-only formalization of Logipedia corpus artifact "fact.axiom_fact"
-- (catalog title "fact.axiom_fact"): the source polymorphic equality relates
-- factorial at a natural argument to the naturally filtered factorial body.
-- This file contains no proof.

namespace fact

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

def filterNatType (R : Type) (body : Nat → R) : Nat → R
  | 0 => body 0
  | Nat.succ n => body (Nat.succ n)

-- itpeval-source-signature: logipedia:fact.fact as factFn
axiom factFn : Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

theorem axiom_fact :
    ∀ n : Nat, sourceEqual Nat (factFn n) (filterNatType Nat factBody n) := sorry

end fact
