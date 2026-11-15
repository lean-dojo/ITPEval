-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_leb"
-- (catalog title "nat.sym_eq_leb"): under the source abstract equality-to-Leibniz
-- bridge and the axiom relating each Boolean less-than-or-equal test to its
-- naturally filtered body, the filtered body is Leibniz-equal in the reverse
-- direction to the test. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : ∀ A : Type, A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.leb as leb
axiom leb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.leb_body as lebBody
axiom lebBody : Nat → Nat → Bool

theorem sym_eq_leb
    (equalLeibniz :
      ∀ (A : Type) (x y : A), sourceEqual A x y →
        ∀ P : A → Prop, P x → P y)
    (axiomLeb :
      ∀ n : Nat,
        sourceEqual (Nat → Bool) (leb n)
          (filterNatType (Nat → Bool) lebBody n)) :
    ∀ n : Nat, ∀ P : (Nat → Bool) → Prop,
      P (filterNatType (Nat → Bool) lebBody n) →
      P (leb n) := sorry

end nat
