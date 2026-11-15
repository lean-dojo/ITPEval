-- Statement-only formalization of Thousand Theorems artifact Q939927
-- (thousand-theorems__lean4__Q939927), "Stone–Weierstrass theorem": a real
-- subalgebra of continuous functions on a compact space is dense when it
-- separates points. This file contains no proof.

module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Algebra.Order.Module.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.Topology.ContinuousMap.Lattice
public import Mathlib.Topology.ContinuousMap.Weierstrass

@[expose] public section

namespace Q939927

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The real Stone–Weierstrass approximation theorem for a compact space. -/
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (A : Subalgebra ℝ C(X, ℝ)) (w : A.SeparatesPoints) :
    A.topologicalClosure = ⊤ := sorry

end Q939927
