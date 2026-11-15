-- Statement-only formalization of Logipedia corpus artifact "connectives.nmk"
-- (catalog title "connectives.nmk"): introduction for the module's abstract
-- negation, deriving sourceNot A from a map A → sourceFalse.
-- This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.False as sourceFalse
axiom sourceFalse : Prop

-- itpeval-source-signature: logipedia:connectives.Not as sourceNot
axiom sourceNot : Prop → Prop

theorem nmk :
    ∀ A : Prop, (A → sourceFalse) → sourceNot A := sorry

end connectives
