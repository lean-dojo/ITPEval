-- Statement-only formalization of Logipedia corpus artifact "connectives.ex_intro"
-- (catalog title "connectives.ex_intro"): introduction for the module's abstract
-- existential connective, deriving sourceEx A P from a witness x satisfying P.
-- This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.ex as sourceEx
axiom sourceEx : (A : Type) → (A → Prop) → Prop

theorem ex_intro :
    ∀ (A : Type) (P : A → Prop) (x : A), P x → sourceEx A P := sorry

end connectives
