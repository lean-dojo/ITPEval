-- Statement-only formalization of Logipedia corpus artifact
-- "nat.sym_eq_minus_body_O" (catalog title "nat.sym_eq_minus_body_O"): Leibniz
-- equality relates the constant-zero function on natural numbers to the
-- subtraction body at zero. This file contains no proof.

namespace nat

-- itpeval-source-signature: logipedia:nat.minus_body as minusBody
axiom minusBody : Nat -> Nat -> Nat

theorem sym_eq_minus_body_O :
    forall P : (Nat -> Nat) -> Prop,
      P (fun _m => 0) ->
      P (minusBody 0) := sorry

end nat
