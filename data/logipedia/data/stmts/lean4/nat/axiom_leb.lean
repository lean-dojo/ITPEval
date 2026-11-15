-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_leb" (catalog title "nat.axiom_leb"): the source polymorphic
-- equality relates each Boolean-valued less-than-or-equal test function to the
-- corresponding naturally filtered comparison-body function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.leb as leb
axiom leb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.leb_body as lebBody
axiom lebBody : Nat → Nat → Bool

theorem axiom_leb :
    ∀ n : Nat,
      equal (Nat → Bool) (leb n)
        (filterNatType (Nat → Bool) lebBody n) := sorry

end nat
