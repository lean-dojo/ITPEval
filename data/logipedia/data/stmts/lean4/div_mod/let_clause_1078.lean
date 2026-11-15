-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.let_clause_1078" (catalog title "div_mod.let_clause_1078"):
-- two natural-number quotient-remainder decompositions, with the first quotient
-- both at most and less than the second, yield the commuted first decomposition.
-- This file contains no proof.

namespace div_mod

def div_mod_spec (a b q r : Nat) : Prop :=
  r < b /\ a = q * b + r

theorem let_clause_1078 :
    forall a b q r q1 r1 : Nat,
      div_mod_spec a b q r ->
      r < b ->
      a = q * b + r ->
      div_mod_spec a b q1 r1 ->
      r1 < b ->
      a = q1 * b + r1 ->
      q <= q1 ->
      q < q1 ->
      a = r + b * q := sorry

end div_mod
