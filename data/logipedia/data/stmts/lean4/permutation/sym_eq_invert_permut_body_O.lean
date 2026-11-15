-- Statement-only formalization of Logipedia corpus artifact
-- "permutation.sym_eq_invert_permut_body_O" (catalog title
-- "permutation.sym_eq_invert_permut_body_O"): Leibniz equality transports every
-- predicate from the function that compares its input with f 0 and returns zero
-- in either Boolean branch to the inverse-permutation body at zero.
-- This file contains no proof.

namespace permutation

def matchBoolType {α : Type u} (caseTrue caseFalse : α) (b : Bool) : α :=
  match b with
  | true => caseTrue
  | false => caseFalse

-- itpeval-source-signature: logipedia:permutation.invert_permut_body as invertPermutBody
axiom invertPermutBody : Nat → (Nat → Nat) → Nat → Nat

theorem sym_eq_invert_permut_body_O :
    ∀ P : ((Nat → Nat) → Nat → Nat) → Prop,
      P (fun f m ↦ matchBoolType 0 0 (m == f 0)) →
      P (invertPermutBody 0) := sorry

end permutation
