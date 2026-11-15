-- Statement-only formalization of Logipedia corpus artifact "connectives.match_Or_prop"
-- (catalog title "connectives.match_Or_prop"): elimination for the module's abstract
-- disjunction, deriving a result from either of its propositions. This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.Or as sourceOr
axiom sourceOr : Prop → Prop → Prop

theorem match_Or_prop :
    ∀ (A B return_ : Prop), (A → return_) → (B → return_) → sourceOr A B → return_ := sorry

end connectives
