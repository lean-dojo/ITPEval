-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.div_mod_spec_to_eq" (catalog title "div_mod.div_mod_spec_to_eq"):
-- two natural-number division-with-remainder specifications for the same
-- dividend and divisor have equal quotients. This file contains no proof.

namespace div_mod

def div_mod_spec (a b q r : Nat) : Prop :=
  r < b /\ a = q * b + r

theorem div_mod_spec_to_eq :
    forall a b q r q1 r1 : Nat,
      div_mod_spec a b q r ->
      div_mod_spec a b q1 r1 ->
      q = q1 := sorry

end div_mod
