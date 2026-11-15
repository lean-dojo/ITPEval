-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.eq_invert_permut" (catalog title
-- "permutation.eq_invert_permut"): each inverse-permutation function is
-- Leibniz-equal to the naturally filtered inverse-permutation body.
-- This file contains no proof.

namespace permutation

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:permutation.invert_permut as invertPermut
axiom invertPermut : Nat → (Nat → Nat) → Nat → Nat

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem eq_invert_permut :
    ∀ n : Nat, ∀ P : ((Nat → Nat) → Nat → Nat) → Prop,
      P (invertPermut n) →
      P (filterNatType ((Nat → Nat) → Nat → Nat) invertPermutBody n) := sorry

end permutation
