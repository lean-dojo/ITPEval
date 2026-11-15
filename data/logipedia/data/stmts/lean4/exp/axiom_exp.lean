-- Statement-only formalization of Logipedia corpus artifact "exp.axiom_exp"
-- (catalog title "exp.axiom_exp"): the source polymorphic equality relates
-- exponentiation at two natural arguments to the naturally filtered
-- exponentiation body. This file contains no proof.

namespace exp

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:exp.exp as expFn
axiom expFn : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:exp.exp_body as expBody
axiom expBody : Nat → Nat → Nat

theorem axiom_exp :
    ∀ (n m : Nat),
      equal Nat (expFn n m) (filterNatType Nat (expBody n) m) := sorry

end exp
