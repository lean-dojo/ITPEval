-- Statement-only formalization of Thousand Theorems artifact Q5638886
-- (thousand-theorems__lean4__Q5638886), "Hahn embedding theorem": every linearly
-- ordered abelian group embeds injectively by an order-preserving additive homomorphism
-- into a real Hahn series while preserving each element's Archimedean class.
-- This file contains no proof.

module

public import Mathlib.Algebra.Order.Module.HahnEmbedding
public import Mathlib.Analysis.RCLike.Basic

@[expose] public section

open ArchimedeanClass HahnSeries

namespace Q5638886

variable (M : Type*) [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

/-- The Hahn embedding theorem for linearly ordered additive commutative groups. -/
theorem hahnEmbedding_isOrderedAddMonoid :
    ∃ f : M →+o Lex ℝ⟦FiniteArchimedeanClass M⟧, Function.Injective f ∧
      ∀ a, .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := sorry

end Q5638886
