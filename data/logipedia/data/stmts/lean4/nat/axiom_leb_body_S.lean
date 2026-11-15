-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_leb_body_S" (catalog title "nat.axiom_leb_body_S"): the source
-- polymorphic equality relates the less-than-or-equal test body at a successor
-- to the Boolean eliminator with a false zero branch and the preceding
-- less-than-or-equal test as its successor branch. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.leb as leb
axiom leb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.leb_body as lebBody
axiom lebBody : Nat → Nat → Bool

theorem axiom_leb_body_S :
    ∀ n : Nat,
      equal (Nat → Bool) (lebBody (Nat.succ n))
        (fun m ↦ matchNatType Bool false (fun q ↦ leb n q) m) := sorry

end nat
