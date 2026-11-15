-- Statement-only formalization of Thousand Theorems artifact Q1144897
-- (thousand-theorems__lean4__Q1144897), "Brouwer fixed-point theorem": every
-- continuous self-map of a nonempty compact convex subset of a finite-dimensional
-- real normed vector space has a fixed point. This file contains no proof.

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.ContinuousMap.Basic

@[expose] public section

namespace Q1144897

/-- Brouwer's fixed-point theorem for finite-dimensional real normed spaces. -/
theorem brouwer_fixed_point {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ (s : Set V), Convex ℝ s → IsCompact s → s.Nonempty →
      ∀ (f : C(s, s)), ∃ x, f x = x := sorry

end Q1144897
