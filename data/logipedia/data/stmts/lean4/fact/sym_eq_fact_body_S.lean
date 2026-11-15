-- Statement-only formalization of Logipedia corpus artifact "fact.sym_eq_fact_body_S"
-- (catalog title "fact.sym_eq_fact_body_S"): Leibniz equality relates the product
-- of factorial at a natural number and its successor to the factorial body at
-- that successor. This file contains no proof.

namespace fact

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:fact.fact as factFn
axiom factFn : Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

theorem sym_eq_fact_body_S :
    ∀ n : Nat,
      Leibniz Nat (factFn n * Nat.succ n) (factBody (Nat.succ n)) := sorry

end fact
