-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_leb_body_S" (catalog title "nat.eq_leb_body_S"): Leibniz equality
-- relates the less-than-or-equal test body at a successor to the Boolean
-- natural-number eliminator with a false zero branch and the preceding
-- less-than-or-equal test as its successor branch. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.leb as leb
axiom leb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.leb_body as lebBody
axiom lebBody : Nat → Nat → Bool

theorem eq_leb_body_S :
    ∀ n : Nat, ∀ P : (Nat → Bool) → Prop,
      P (lebBody (Nat.succ n)) →
      P (fun m ↦ matchNatType Bool false (fun q ↦ leb n q) m) := sorry

end nat
