-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.sym_eq_gcd_aux_body_O" (catalog title "gcd.sym_eq_gcd_aux_body_O"):
-- the binary natural-number function returning its first input is Leibniz-equal
-- to the zero-indexed auxiliary greatest-common-divisor body.
-- This file contains no proof.

namespace gcd

-- itpeval-source-signature: logipedia:gcd.gcd_aux_body as gcdAuxBody
axiom gcdAuxBody : Nat → Nat → Nat → Nat

theorem sym_eq_gcd_aux_body_O :
    ∀ P : (Nat → Nat → Nat) → Prop,
      P (fun (m _n : Nat) ↦ m) →
      P (gcdAuxBody 0) := sorry

end gcd
