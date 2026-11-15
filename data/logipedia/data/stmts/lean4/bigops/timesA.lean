-- Statement-only formalization of Logipedia corpus artifact "bigops.timesA"
-- (catalog title "bigops.timesA"): the source module's opaque Aop predicate
-- holds for the natural number one. This file contains no proof.

namespace bigops

-- itpeval-source-signature: logipedia:bigops.Aop as Aop
axiom Aop : (A : Type) → A → Prop

theorem timesA :
    Aop Nat 1 := sorry

end bigops
