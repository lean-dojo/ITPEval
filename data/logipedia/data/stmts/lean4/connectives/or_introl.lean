-- Statement-only formalization of Logipedia corpus artifact "connectives.or_introl"
-- (catalog title "connectives.or_introl"): introduction for the module's abstract
-- disjunction, deriving sourceOr A B from proposition A. This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.Or as sourceOr
axiom sourceOr : Prop → Prop → Prop

theorem or_introl :
    ∀ (A B : Prop), A → sourceOr A B := sorry

end connectives
