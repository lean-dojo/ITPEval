-- Statement-only formalization of Logipedia corpus artifact "nat.eq_eqb"
-- (catalog title "nat.eq_eqb"): each partially applied Boolean equality-test
-- function is Leibniz-equal to its naturally filtered body. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.eqb as eqb
axiom eqb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.eqb_body as eqbBody
axiom eqbBody : Nat → Nat → Bool

theorem eq_eqb :
    ∀ n : Nat, ∀ P : (Nat → Bool) → Prop,
      P (eqb n) →
      P (filterNatType (Nat → Bool) eqbBody n) := sorry

end nat
