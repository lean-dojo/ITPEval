-- Statement-only formalization of Thousand Theorems artifact Q1149458
-- (thousand-theorems__lean4__Q1149458), "Compactness theorem": a first-order
-- theory is satisfiable if and only if every finite subtheory is satisfiable.
-- This file contains no proof.

module

public import Mathlib.ModelTheory.Satisfiability

@[expose] public section

universe u v

namespace FirstOrder.Language.Theory

namespace Q1149458

/-- The compactness theorem for first-order logic. -/
theorem isSatisfiable_iff_isFinitelySatisfiable
    {L : Language.{u, v}} {T : L.Theory} :
    T.IsSatisfiable ↔ T.IsFinitelySatisfiable := sorry

end Q1149458

end FirstOrder.Language.Theory
