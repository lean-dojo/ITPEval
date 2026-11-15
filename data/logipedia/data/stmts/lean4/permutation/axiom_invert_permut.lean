-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.axiom_invert_permut" (catalog title
-- "permutation.axiom_invert_permut"): the source polymorphic equality relates
-- each inverse-permutation function to its naturally filtered body function.
-- This file contains no proof.

namespace permutation

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:permutation.invert_permut as invertPermut
axiom invertPermut : Nat → (Nat → Nat) → Nat → Nat

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem axiom_invert_permut :
    ∀ n : Nat,
      equal ((Nat → Nat) → Nat → Nat) (invertPermut n)
        (filterNatType ((Nat → Nat) → Nat → Nat) invertPermutBody n) := sorry

end permutation
