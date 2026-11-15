-- Statement-only formalization of Logipedia corpus artifact "connectives.falsity"
-- (catalog title "connectives.falsity"): elimination from the module's abstract
-- falsity proposition, deriving any proposition. This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.False as sourceFalse
axiom sourceFalse : Prop

theorem falsity :
    ∀ t : Prop, sourceFalse → t := sorry

end connectives
