-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.axiom_gcd_aux" (catalog title "gcd.axiom_gcd_aux"): the source
-- polymorphic equality relates each greatest-common-divisor auxiliary function
-- to the corresponding naturally filtered auxiliary body function.
-- This file contains no proof.

namespace gcd

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:gcd.gcd_aux as gcdAux
axiom gcdAux : Nat → Nat → Nat → Nat

-- itpeval-source-signature: logipedia:gcd.gcd_aux_body as gcdAuxBody
axiom gcdAuxBody : Nat → Nat → Nat → Nat

theorem axiom_gcd_aux :
    ∀ p : Nat,
      equal (Nat → Nat → Nat) (gcdAux p)
        (filterNatType (Nat → Nat → Nat) gcdAuxBody p) := sorry

end gcd
