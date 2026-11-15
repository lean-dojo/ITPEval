-- Statement-only formalization of Thousand Theorems artifact Q1471282
-- (thousand-theorems__lean4__Q1471282), "Radon's theorem": every affine-dependent
-- family over a strictly ordered field has a subset whose image and complementary
-- image have intersecting convex hulls. This file contains no proof.

module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.AffineSpace.Independent

public section

open Fintype Finset Set

namespace Q1471282

variable {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Radon's theorem: an affine-dependent family has complementary parts with
intersecting convex hulls. -/
theorem radon_partition {f : ι → E} (h : ¬ AffineIndependent 𝕜 f) :
    ∃ I, (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := sorry

end Q1471282
