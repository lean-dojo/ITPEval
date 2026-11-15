-- Statement-only formalization of Logipedia corpus artifact "connectives.conj"
-- (catalog title "connectives.conj"): introduction for the module's abstract
-- conjunction, deriving sourceAnd A B from propositions A and B.
-- This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.And as sourceAnd
axiom sourceAnd : Prop → Prop → Prop

theorem conj :
    ∀ (A B : Prop), A → B → sourceAnd A B := sorry

end connectives
