-- Statement-only formalization of Logipedia corpus artifact "fact.sym_eq_fact"
-- (catalog title "fact.sym_eq_fact"): Leibniz equality relates the naturally
-- filtered factorial body at a natural argument to factorial at that argument.
-- This file contains no proof.

namespace fact

def Leibniz (A : Type) (x y : A) : Prop :=
  ∀ P : A → Prop, P x → P y

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:fact.fact as factFn
axiom factFn : Nat → Nat

-- itpeval-source-signature: logipedia:fact.fact_body as factBody
axiom factBody : Nat → Nat

theorem sym_eq_fact :
    ∀ n : Nat, Leibniz Nat (filterNatType Nat factBody n) (factFn n) := sorry

end fact
