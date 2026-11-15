-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.sym_eq_gcd_aux" (catalog title "gcd.sym_eq_gcd_aux"): for every natural
-- recursion index, the natural-type filter of the auxiliary greatest-common-divisor
-- body is Leibniz-equal, as a binary natural-number function, to the auxiliary
-- greatest-common-divisor function at that index. This file contains no proof.

namespace gcd

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:gcd.gcd_aux as gcdAux
axiom gcdAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:gcd.gcd_aux_body as gcdAuxBody
axiom gcdAuxBody : Nat → Nat → Nat → Nat

theorem sym_eq_gcd_aux :
    ∀ p : Nat, ∀ P : (Nat → Nat → Nat) → Prop,
      P (filterNatType (Nat → Nat → Nat) gcdAuxBody p) →
      P (gcdAux p) := sorry

end gcd
