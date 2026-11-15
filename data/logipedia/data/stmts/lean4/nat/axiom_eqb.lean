-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_eqb" (catalog title "nat.axiom_eqb"): the source polymorphic
-- equality relates each Boolean-valued equality-test function to the corresponding
-- naturally filtered equality-test body function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.eqb as eqb
axiom eqb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.eqb_body as eqbBody
axiom eqbBody : Nat → Nat → Bool

theorem axiom_eqb :
    ∀ n : Nat,
      equal (Nat → Bool) (eqb n)
        (filterNatType (Nat → Bool) eqbBody n) := sorry

end nat
