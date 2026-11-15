-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.axiom_invert_permut_body_S" (catalog title
-- "permutation.axiom_invert_permut_body_S"): the source polymorphic equality
-- identifies each successor inverse-permutation body with its Boolean-
-- conditional natural-number function. This file contains no proof.

namespace permutation

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:bool.match_bool_type as matchBoolType
axiom matchBoolType : (A : Type) → A → A → Bool → A

-- itpeval-source-signature: logipedia:nat.eqb as eqb
axiom eqb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:permutation.invert_permut as invertPermut
axiom invertPermut : Nat → (Nat → Nat) → Nat → Nat

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem axiom_invert_permut_body_S :
    ∀ n : Nat,
      equal ((Nat → Nat) → Nat → Nat) (invertPermutBody (Nat.succ n))
        (fun f m ↦
          matchBoolType Nat (Nat.succ n) (invertPermut n f m)
            (eqb m (f (Nat.succ n)))) := sorry

end permutation
