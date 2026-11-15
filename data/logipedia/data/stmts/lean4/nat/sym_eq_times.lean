-- Statement-only formalization of Logipedia corpus artifact "nat.sym_eq_times"
-- (catalog title "nat.sym_eq_times"): each naturally filtered natural-number
-- multiplication-body function is Leibniz-equal to the corresponding partially
-- applied multiplication function. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.times as times
axiom times : Nat → Nat → Nat

-- itpeval-source-signature: logipedia:nat.times_body as timesBody
axiom timesBody : Nat → Nat → Nat

theorem sym_eq_times :
    ∀ n : Nat, ∀ P : (Nat → Nat) → Prop,
      P (filterNatType (Nat → Nat) timesBody n) →
      P (times n) := sorry

end nat
