-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.let_clause_1062" (catalog title "div_mod.let_clause_1062"):
-- two natural-number quotient-remainder decompositions, with the first quotient
-- not at most the second, yield the commuted second decomposition. This file contains no proof.

namespace div_mod

def div_mod_spec (a b q r : Nat) : Prop :=
  r < b /\ a = q * b + r

theorem let_clause_1062 :
    forall a b q r q1 r1 : Nat,
      div_mod_spec a b q r ->
      r < b ->
      a = q * b + r ->
      div_mod_spec a b q1 r1 ->
      r1 < b ->
      a = q1 * b + r1 ->
      not (q <= q1) ->
      a = r1 + b * q1 := sorry

end div_mod
