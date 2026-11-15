-- Statement-only formalization of Logipedia corpus artifact "connectives.Not_ind"
-- (catalog title "connectives.Not_ind"): elimination for the module's abstract
-- negation, deriving Q from a map (A → False) → Q and an inhabitant of Not A.
-- This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.False as sourceFalse
axiom sourceFalse : Prop

-- itpeval-source-signature: logipedia:connectives.Not as sourceNot
axiom sourceNot : Prop → Prop

theorem Not_ind :
    ∀ (A Q : Prop), ((A → sourceFalse) → Q) → sourceNot A → Q := sorry

end connectives
