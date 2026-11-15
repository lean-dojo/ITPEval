-- Statement-only formalization of "Brouwer Fixed Point Theorem" from Hundred Theorems item 036.
-- Every continuous self-map of a nonempty compact convex subset of a finite-dimensional real
-- Euclidean space has a fixed point. This file contains no proof.

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Basic

public section

namespace Theorems100

/-- Brouwer's fixed point theorem for finite-dimensional real Euclidean spaces. -/
theorem brouwer_fixed_point_theorem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Set E) (hs_compact : IsCompact s) (hs_convex : Convex ℝ s)
    (hs_nonempty : s.Nonempty) (f : E → E) (hf_continuous : ContinuousOn f s)
    (hf_self_map : Set.MapsTo f s s) :
    ∃ x ∈ s, f x = x := sorry

end Theorems100
