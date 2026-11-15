-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.eq_gcd_aux" (catalog title "gcd.eq_gcd_aux"): for every natural recursion
-- index, the auxiliary greatest-common-divisor function is Leibniz-equal, as a
-- binary natural-number function, to the natural-type filter of its body at
-- that index. This file contains no proof.

namespace gcd

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:gcd.gcd_aux as gcdAux
axiom gcdAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:gcd.gcd_aux_body as gcdAuxBody
axiom gcdAuxBody : Nat → Nat → Nat → Nat

theorem eq_gcd_aux :
    ∀ p : Nat, ∀ P : (Nat → Nat → Nat) → Prop,
      P (gcdAux p) →
      P (filterNatType (Nat → Nat → Nat) gcdAuxBody p) := sorry

end gcd
