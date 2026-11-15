-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_eqb_body_O" (catalog title "nat.eq_eqb_body_O"): Leibniz equality
-- relates the equality-test body at zero to the Boolean natural-number
-- eliminator with a true zero branch and a constant-false successor branch.
-- This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.eqb_body as eqbBody
axiom eqbBody : Nat → Nat → Bool

theorem eq_eqb_body_O :
    ∀ P : (Nat → Bool) → Prop,
      P (eqbBody 0) →
      P (fun m ↦ matchNatType Bool true (fun _q ↦ false) m) := sorry

end nat
