-- Statement-only formalization of Logipedia corpus artifact
-- "nat.axiom_eqb_body_O" (catalog title "nat.axiom_eqb_body_O"): the source
-- polymorphic equality relates the equality-test body at zero to the Boolean
-- eliminator with a true zero branch and a constant-false successor branch.
-- This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.eqb_body as eqbBody
axiom eqbBody : Nat → Nat → Bool

theorem axiom_eqb_body_O :
    equal (Nat → Bool) (eqbBody 0)
      (fun m ↦ matchNatType Bool true (fun _q ↦ false) m) := sorry

end nat
