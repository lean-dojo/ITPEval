-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.sym_eq_invert_permut" (catalog title
-- "permutation.sym_eq_invert_permut"): natural filtering of the
-- inverse-permutation body at each index is Leibniz-equal to the corresponding
-- inverse-permutation function. This file contains no proof.

namespace permutation

-- itpeval-source-signature: logipedia:nat.filter_nat_type as filterNatType
axiom filterNatType : (R : Type) → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:permutation.invert_permut as invertPermut
axiom invertPermut : Nat → (Nat → Nat) → Nat → Nat

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem sym_eq_invert_permut :
    ∀ n : Nat, ∀ P : ((Nat → Nat) → Nat → Nat) → Prop,
      P (filterNatType ((Nat → Nat) → Nat → Nat) invertPermutBody n) →
      P (invertPermut n) := sorry

end permutation
