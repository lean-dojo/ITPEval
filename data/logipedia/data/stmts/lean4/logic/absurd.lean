-- Statement-only formalization of Logipedia corpus artifact "logic.absurd"
-- (catalog title "logic.absurd"): an inhabited proposition and its negation
-- under the fixed source connectives imply source falsity. This file contains no proof.

namespace logic

-- itpeval-source-signature: logipedia:connectives.False as sourceFalse
axiom sourceFalse : Prop

-- itpeval-source-signature: logipedia:connectives.Not as sourceNot
axiom sourceNot : Prop -> Prop

theorem absurd :
    forall A : Prop, A -> sourceNot A -> sourceFalse := sorry

end logic
