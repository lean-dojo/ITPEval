-- Statement-only formalization of Logipedia corpus artifact "fact.axiom_fact_body_S"
-- (catalog title "fact.axiom_fact_body_S"): the source polymorphic equality relates
-- the factorial body at a successor to the product of factorial at its predecessor
-- and that successor. This file contains no proof.

namespace fact

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:fact.fact as factFn
axiom factFn : Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

theorem axiom_fact_body_S :
    ∀ n : Nat,
      sourceEqual Nat (factBody (Nat.succ n)) (factFn n * Nat.succ n) := sorry

end fact
