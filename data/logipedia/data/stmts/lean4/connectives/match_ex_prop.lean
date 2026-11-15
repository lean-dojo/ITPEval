-- Statement-only formalization of Logipedia corpus artifact "connectives.match_ex_prop"
-- (catalog title "connectives.match_ex_prop"): elimination for the module's abstract
-- existential connective, deriving a result from a handler for every witness satisfying
-- the predicate. This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.ex as sourceEx
axiom sourceEx : ∀ A : Type, (A → Prop) → Prop

theorem match_ex_prop :
    ∀ (A : Type) (P : A → Prop) (return_ : Prop),
      (∀ x : A, P x → return_) → sourceEx A P → return_ := sorry

end connectives
