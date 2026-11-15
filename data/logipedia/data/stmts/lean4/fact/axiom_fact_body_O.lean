-- Statement-only formalization of Logipedia corpus artifact "fact.axiom_fact_body_O"
-- (catalog title "fact.axiom_fact_body_O"): the source polymorphic equality relates
-- the factorial body at zero to the successor of zero. This file contains no proof.

namespace fact

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

theorem axiom_fact_body_O :
    equal Nat (factBody 0) (Nat.succ 0) := sorry

end fact
