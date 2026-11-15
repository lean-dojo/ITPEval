-- Statement-only formalization of Logipedia corpus artifact "nat.eq_leb"
-- (catalog title "nat.eq_leb"): each partially applied Boolean less-than-or-equal
-- test function is Leibniz-equal to its naturally filtered body. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.leb as leb
axiom leb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.leb_body as lebBody
axiom lebBody : Nat → Nat → Bool

theorem eq_leb :
    ∀ n : Nat, ∀ P : (Nat → Bool) → Prop,
      P (leb n) →
      P (filterNatType (Nat → Bool) lebBody n) := sorry

end nat
