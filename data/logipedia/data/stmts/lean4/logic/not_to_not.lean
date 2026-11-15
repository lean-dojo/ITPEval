-- Statement-only formalization of Logipedia corpus artifact "logic.not_to_not"
-- (catalog title "logic.not_to_not"): contraposition for the module's abstract
-- fixed negation, transporting sourceNot B to sourceNot A along a map A -> B.
-- This file contains no proof.

namespace logic

-- itpeval-source-signature: logipedia:connectives.Not as sourceNot
axiom sourceNot : Prop -> Prop

theorem not_to_not :
    forall (A B : Prop), (A -> B) -> sourceNot B -> sourceNot A := sorry

end logic
