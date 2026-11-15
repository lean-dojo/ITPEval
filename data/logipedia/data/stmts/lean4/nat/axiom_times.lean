-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_times" (catalog title "nat.axiom_times"): the source polymorphic
-- equality relates each natural-number multiplication function to the corresponding
-- naturally filtered multiplication-body function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat → Nat → Nat

theorem axiom_times :
    ∀ n : Nat,
      equal (Nat → Nat) (times n)
        (filterNatType (Nat → Nat) timesBody n) := sorry

end nat
