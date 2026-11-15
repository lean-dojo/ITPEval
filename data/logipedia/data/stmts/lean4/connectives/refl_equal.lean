-- Statement-only formalization of Logipedia corpus artifact "connectives.refl_equal"
-- (catalog title "connectives.refl_equal"): reflexivity of the module's abstract
-- equality relation for every type and element. This file contains no proof.

namespace connectives

-- itpeval-source-signature: logipedia:connectives.equal as sourceEqual
axiom sourceEqual : (A : Type) → A → A → Prop

theorem refl_equal :
    ∀ (A : Type) (x : A), sourceEqual A x x := sorry

end connectives
