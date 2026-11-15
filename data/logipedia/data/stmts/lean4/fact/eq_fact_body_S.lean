-- Statement-only formalization of Logipedia corpus artifact "fact.eq_fact_body_S"
-- (catalog title "fact.eq_fact_body_S"): Leibniz equality relates the factorial
-- body at a successor to the product of factorial at its predecessor and that
-- successor. This file contains no proof.

namespace fact

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact as factFn
axiom factFn : Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

theorem eq_fact_body_S :
    ∀ n : Nat,
      Leibniz Nat (factBody (Nat.succ n)) (times (factFn n) (Nat.succ n)) := sorry

end fact
