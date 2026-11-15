-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.eq_gcd_aux_body_O" (catalog title "gcd.eq_gcd_aux_body_O"):
-- the zero-indexed auxiliary greatest-common-divisor body is Leibniz-equal,
-- as a binary natural-number function, to the function returning its first input.
-- This file contains no proof.

namespace gcd

-- itpeval-source-signature: logipedia:gcd.gcd_aux_body as gcdAuxBody
axiom gcdAuxBody : Nat → Nat → Nat → Nat

theorem eq_gcd_aux_body_O :
    ∀ P : (Nat → Nat → Nat) → Prop,
      P (gcdAuxBody 0) →
      P (fun (m _n : Nat) ↦ m) := sorry

end gcd
