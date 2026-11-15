-- Statement-only formalization of Logipedia corpus artifact
-- "gcd.axiom_gcd_aux_body_O" (catalog title "gcd.axiom_gcd_aux_body_O"):
-- the source polymorphic equality relates the zero-indexed greatest-common-divisor
-- auxiliary body to the binary natural-number function that returns its first input.
-- This file contains no proof.

namespace gcd

-- itpeval-source-signature: logipedia:connectives.equal as equal
axiom equal : (A : Type) → A → A → Prop

-- itpeval-source-signature: logipedia:gcd.gcd_aux_body as gcdAuxBody
axiom gcdAuxBody : Nat → Nat → Nat → Nat

theorem axiom_gcd_aux_body_O :
    equal (Nat → Nat → Nat) (gcdAuxBody 0) (fun (m _n : Nat) ↦ m) := sorry

end gcd
