-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.div_mod_spec_intro" (catalog title "div_mod.div_mod_spec_intro"):
-- natural-number quotient and remainder bounds and decomposition introduce the
-- division-with-remainder specification. This file contains no proof.

namespace div_mod

def div_mod_spec (n m q r : Nat) : Prop :=
  r < m /\ n = q * m + r

theorem div_mod_spec_intro :
    forall n m q r : Nat,
      r < m -> n = q * m + r -> div_mod_spec n m q r := sorry

end div_mod
