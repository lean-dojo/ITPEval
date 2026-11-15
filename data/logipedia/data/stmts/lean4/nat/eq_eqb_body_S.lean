-- Statement-only formalization of Logipedia corpus artifact
-- "nat.eq_eqb_body_S" (catalog title "nat.eq_eqb_body_S"): Leibniz equality
-- relates the equality-test body at a successor to the Boolean natural-number
-- eliminator with a false zero branch and the preceding equality test as its
-- successor branch. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.match_nat_type as matchNatType
axiom matchNatType : (R : Type) → R → (Nat → R) → Nat → R

-- itpeval-source-signature: logipedia:nat.eqb as eqb
axiom eqb : Nat → Nat → Bool

-- itpeval-source-signature: logipedia:nat.eqb_body as eqbBody
axiom eqbBody : Nat → Nat → Bool

theorem eq_eqb_body_S :
    ∀ n : Nat, ∀ P : (Nat → Bool) → Prop,
      P (eqbBody (Nat.succ n)) →
      P (fun m ↦ matchNatType Bool false (fun q ↦ eqb n q) m) := sorry

end nat
