-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_plus" (catalog title "nat.axiom_plus"): the source polymorphic
-- equality relates each natural-number addition function to the corresponding
-- naturally filtered addition-body function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.plus as plus
axiom plus : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.plus_body as plusBody
axiom plusBody : Nat → Nat → Nat

theorem axiom_plus :
    ∀ n : Nat,
      equal (Nat → Nat) (plus n)
        (filterNatType (Nat → Nat) plusBody n) := sorry

end nat
