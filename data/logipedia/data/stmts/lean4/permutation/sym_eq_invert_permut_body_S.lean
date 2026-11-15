-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.sym_eq_invert_permut_body_S" (catalog title
-- "permutation.sym_eq_invert_permut_body_S"): Leibniz equality transports every
-- predicate from the function that returns the successor at its image and
-- otherwise uses the preceding inverse to the successor inverse-permutation body.
-- This file contains no proof.

namespace permutation

def matchBoolType {α : Type u} (caseTrue caseFalse : α) (b : Bool) : α :=
  match b with
  | true => caseTrue
  | false => caseFalse

-- itpeval-source-signature: logipedia:permutation.invert_permut as invertPermut
axiom invertPermut : Nat → (Nat → Nat) → Nat → Nat

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem sym_eq_invert_permut_body_S :
    ∀ n : Nat, ∀ P : ((Nat → Nat) → Nat → Nat) → Prop,
      P (fun f m ↦
        matchBoolType (Nat.succ n) (invertPermut n f m)
          (m == f (Nat.succ n))) →
      P (invertPermutBody (Nat.succ n)) := sorry

end permutation
