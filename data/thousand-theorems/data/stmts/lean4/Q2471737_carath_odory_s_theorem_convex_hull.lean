-- Statement-only formalization of Thousand Theorems artifact Q2471737
-- (thousand-theorems__lean4__Q2471737), "Carathéodory's theorem (convex hull)":
-- over a strictly ordered field, the convex hull of a set is the union of the convex
-- hulls of its finite affine-independent subsets. This file contains no proof.

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Independent

public section

open Set Finset

universe u

namespace Q2471737

variable {𝕜 : Type*} {E : Type u} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Carathéodory's convexity theorem. -/
theorem convexHull_eq_union {s : Set E} : convexHull 𝕜 s =
    ⋃ (t : Finset E) (_ : ↑t ⊆ s) (_ : AffineIndependent 𝕜 ((↑) : t → E)), convexHull 𝕜 ↑t :=
  sorry

end Q2471737
