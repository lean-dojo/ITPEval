-- Statement-only formalization of Logipedia corpus artifact
-- "div_mod.match_div_mod_spec_prop" (catalog title "div_mod.match_div_mod_spec_prop"):
-- elimination of a natural-number division-with-remainder specification into
-- an arbitrary proposition. This file contains no proof.

namespace div_mod

def div_mod_spec (n m q r : Nat) : Prop :=
  r < m /\ n = q * m + r

theorem match_div_mod_spec_prop :
    forall n m q r : Nat, forall return_ : Prop,
      (r < m -> n = q * m + r -> return_) ->
      div_mod_spec n m q r ->
      return_ := sorry

end div_mod
