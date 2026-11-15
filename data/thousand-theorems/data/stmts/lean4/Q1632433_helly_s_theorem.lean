-- Statement-only formalization of Thousand Theorems artifact Q1632433
-- (thousand-theorems__lean4__Q1632433), "Helly's theorem": a finite family of
-- convex sets in a finite-dimensional vector space has nonempty total intersection
-- when it has at least dimension-plus-one members and every subfamily of exactly
-- that size intersects.
-- This file contains no proof.

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

open Fintype Finset Set

namespace Q1632433

open Module

variable {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Helly's theorem for a finite family of convex sets in its classical form. -/
theorem helly_theorem {F : ι → Set E} {s : Finset ι}
    (h_card : finrank 𝕜 E + 1 ≤ #s)
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, #I = finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) :
    (⋂ i ∈ s, F i).Nonempty := sorry

end Q1632433
