-- Statement-only formalization of Thousand Theorems artifact Q642620
-- (thousand-theorems__lean4__Q642620), "Krein–Milman theorem": a compact convex
-- set in a real locally convex topological vector space is the closure of the
-- convex hull of its extreme points. This file contains no proof.

module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Topology.Algebra.Module.LocallyConvex

public section

open Set

namespace Q642620

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [T2Space E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] {s : Set E}

/-- The Krein–Milman theorem for a compact convex set in a real LCTVS. -/
theorem closure_convexHull_extremePoints (hscomp : IsCompact s) (hAconv : Convex ℝ s) :
    closure (convexHull ℝ <| s.extremePoints ℝ) = s := sorry

end Q642620
