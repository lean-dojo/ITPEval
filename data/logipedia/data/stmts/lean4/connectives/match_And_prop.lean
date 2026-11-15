-- Statement-only formalization of Logipedia corpus artifact "connectives.match_And_prop"
-- (catalog title "connectives.match_And_prop"): elimination for the module's abstract
-- conjunction, deriving a result from its left and right propositions. This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.And as sourceAnd
axiom sourceAnd : Prop → Prop → Prop

theorem match_And_prop :
    ∀ (A B return_ : Prop), (A → B → return_) → sourceAnd A B → return_ := sorry

end connectives
