-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.eq_invert_permut_body_O" (catalog title
-- "permutation.eq_invert_permut_body_O"): Leibniz equality transports every
-- predicate from the inverse-permutation body at zero to the function that
-- compares its input with f 0 and returns zero in either Boolean branch.
-- This file contains no proof.

namespace permutation

def matchBoolType {α : Type u} (caseTrue caseFalse : α) (b : Bool) : α :=
  match b with
  | true => caseTrue
  | false => caseFalse

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem eq_invert_permut_body_O :
    ∀ P : ((Nat → Nat) → Nat → Nat) → Prop,
      P (invertPermutBody 0) →
      P (fun f m ↦ matchBoolType 0 0 (m == f 0)) := sorry

end permutation
