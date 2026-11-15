-- Statement-only formalization of Logipedia corpus artifact "connectives.or_intror"
-- (catalog title "connectives.or_intror"): right introduction for the module's
-- abstract disjunction, deriving sourceOr A B from proposition B.
-- This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.Or as sourceOr
axiom sourceOr : Prop → Prop → Prop

theorem or_intror :
    ∀ (A B : Prop), B → sourceOr A B := sorry

end connectives
