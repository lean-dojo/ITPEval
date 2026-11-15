-- Statement-only formalization of Logipedia corpus artifact "bigops.timesAC"
-- (catalog title "bigops.timesAC"): the source module's opaque ACop predicate
-- holds for the natural number one. This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:bigops.ACop as ACop
axiom ACop : (A : Type) → A → Prop

theorem timesAC :
    ACop Nat 1 := sorry

end bigops
